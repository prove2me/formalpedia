-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_lemma_5_5
-- name    : ShiAuthentication.BA.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:24:37.26143+00:00
-- url     : https://prove2.me/theorems/1496de2d-7480-4a33-aeeb-603ac7882303
-- title:
--   Lemma 5.5 — receiver cut condition
-- statement:
--   Let $n\ge 3$ and $1\le t<n$, let $S$ be the designated sender, and suppose $\mathrm{BB}(G,S,t)$ is feasible: some deterministic protocol solves Byzantine broadcast from $S$ with fault bound $t$ on the public authentication graph $G$. Let $W\subseteq P$ contain $S$, and let $A,B\subseteq P\setminus W$ be nonempty disjoint sets with
--   $$n-2t+|W|\le |A|,|B|\le t-|W|,\qquad |A|+|B|<n-|W|.$$
--   Then there is a receiver $z\notin W$ with
--   $$\widehat V_z\cap A\neq\emptyset,\qquad \widehat V_z\cap B\neq\emptyset,$$
--   where $\widehat V_z=\{z\}\cup V_z$ is the verifier set of $z$ together with $z$ itself.
--
--   This necessary condition on broadcast-feasible graphs is the starting point of every broadcast lower bound in §5 (Corollary 5.6, Lemma 5.8, Theorem 5.10).
--
--   Differences from the source:
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
--   - encoding: the size conditions on |A|, |B|, |W| → the same inequalities in ℤ; reason: avoids truncated natural subtraction in t − |W| and n − 2t + |W|
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Lemma 5.5, p. 26

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Lemma 5.5 (Receiver cut condition)**, p. 26. Let `n ≥ 3`, `1 ≤ t < n`, and suppose
`BB(G, S, t)` is feasible (public authentication graph). For every `W ⊆ P` containing `S` and
every pair of nonempty disjoint sets `A, B ⊆ P \ W` with
`n − 2t + |W| ≤ |A|, |B| ≤ t − |W|` and `|A| + |B| < n − |W|` (compared in `ℤ`), some receiver
`z ∉ W` has `V̂_z ∩ A ≠ ∅` and `V̂_z ∩ B ≠ ∅`, where `V̂_z = {z} ∪ V_z`. -/
theorem lemma_5_5 (n t : ℕ) (hn : 3 ≤ n) (ht1 : 1 ≤ t) (htn : t < n) (G : AuthGraph n)
    (S : Fin n) (hBB : BBPossible .publicGraph t G S) (W : Finset (Fin n)) (hSW : S ∈ W)
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hAlo : (n : ℤ) - 2 * t + W.card ≤ A.card) (hBlo : (n : ℤ) - 2 * t + W.card ≤ B.card)
    (hAhi : (A.card : ℤ) ≤ t - W.card) (hBhi : (B.card : ℤ) ≤ t - W.card)
    (hsum : (A.card : ℤ) + B.card < n - W.card) :
    ∃ z : Fin n, z ∉ W ∧ (closedVerifiers G z ∩ A).Nonempty ∧
      (closedVerifiers G z ∩ B).Nonempty := by sorry

end ShiAuthentication.BA.Supplement
