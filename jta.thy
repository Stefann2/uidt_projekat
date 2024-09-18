theory jta
  imports Main

begin


primrec boustrophedon :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "\<box>" 65) where
  "[] \<box> ys = ys" |
  "(x # xs) \<box> ys = ys @ [x] @ (xs \<box> rev ys)"

fun bumpBy :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "bumpBy k [] = []" |
  "bumpBy k [a] = [a + k]" |
  "bumpBy k (a # b # as) = (a + k) # b # bumpBy k as" 

(* bumpBy 3 [1,2,3,4,5] = [4,2,6,4,8]
  bumpBy 3 [1,2,3,4] = [4,2,6,4]
  bumpBy 3 [1,2] @ [3,4] = [4, 2] @ [6, 4]
  bumpBy 3 1 # [2] @ 3 # [4] = [4, 2] @ [6, 4]
  bumpBy 3 [1,2,3] @ [4] = [4,2,6] @ [7] x x x x
  bumpBy 3 [1] @ 3 # [4] = [4, 2] @ [6, 4]
*)

    
primrec jcode :: "nat \<Rightarrow> nat list" where
  "jcode 0 = []" |
  "jcode (Suc n) = (bumpBy 1 (jcode n)) \<box> (rev  [1..<(Suc n)])"


primrec bumpDn :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bumpDn k 0 = []" |
  "bumpDn k (Suc n) = bumpBy k (rev [1..<(Suc n)])"


primrec code :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "code k 0 = []" |
  "code k (Suc n) = code (if odd (Suc n) then k + 1 else 1) n \<box> bumpDn k (Suc n)"


definition boxall :: "'a list list \<Rightarrow> 'a list" where
  "boxall xs = foldr (\<box>) xs []"

primrec pairs :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "pairs k 0 = []" |
  "pairs k (Suc n) = pairs (if odd (Suc n) then k + 1 else 1) n @ [(k, Suc n)]"

primrec addpair :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list" where
  "addpair k 0 ps = ps" |
  "addpair k (Suc n) ps = addpair (if odd (Suc n) then k + 1 else 1) n ((k, Suc n) # ps)"

definition jcode1 :: "nat \<Rightarrow> nat list" where
  "jcode1 n = boxall (map (\<lambda>(k, m). bumpDn k m) (pairs 0 n))"

fun prologDn :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
  "prologDn k n = (k, k, n-1, 1)"

fun stepDn :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> (nat \<times> nat \<times> nat \<times> nat)) option" where
  "stepDn (j, k, m, n) = (if m < n then None else Some (m + j, (k - j, k, m - 1, n)))"

primrec bumpDn1_pom :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bumpDn1_pom k 0 _ = []" |
  "bumpDn1_pom k (Suc n) parity = 
     (let m = (Suc n) - 1 in 
      if m < 1 then []
      else (if even parity then (m + k) else m)  # bumpDn1_pom k n (parity+1))"

definition bumpDn1 :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bumpDn1 k n = bumpDn1_pom k n 0"


lemma bumpDn_eq_bumpDn1:
  shows "bumpDn k n = bumpDn1 k n"
  unfolding bumpDn1_def
  apply (induction n)
   apply auto
  sorry

fun prologUp :: "nat \<times> nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)" where
  "prologUp (k, n) = (if even n then k else 0, k, 1, n - 1)"

fun stepUp :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (nat \<times> (nat \<times> nat \<times> nat \<times> nat)) option" where
  "stepUp (j, k, m, n) = (if m > n then None else Some (m + j, (k - j, k, m + 1, n)))"

type_synonym 'a queue = "'a list" (* Queue as a list for simplicity *)

fun insert :: "'a list \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "insert xs q = xs @ q"

fun remove :: "'a queue \<Rightarrow> ('a \<times> 'a queue)" where
  "remove [] = (undefined, [])" (* Handle empty case separately *)
  | "remove (x # xs) = (x, xs)"

fun isempty :: "'a queue \<Rightarrow> bool" where
  "isempty q = (q = [])"

fun consQueue :: "'a queue \<Rightarrow> 'a queue list \<Rightarrow> 'a queue list" where
  "consQueue xs xss = (if (isempty xs) then xss else (xs # xss))"

fun wrapQueue :: "'a queue \<Rightarrow> 'a queue list" where
  "wrapQueue xs = consQueue xs []"

primrec mix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "mix [] ys sy = ys"
  | "mix (x # xs) ys sy = insert ys (Node x (mix xs (sy, ys)))"

fun op :: "'a list \<Rightarrow> ('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)" where
  "op xs (ys, sy) = (if even (length xs)
    then (mix xs (ys, sy), mix (rev xs) (sy, ys))
    else (mix xs (ys, sy), mix (rev xs) (ys, sy)))"


end