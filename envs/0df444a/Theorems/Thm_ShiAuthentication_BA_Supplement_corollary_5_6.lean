-- Prove2me | Theorems.Thm_ShiAuthentication_BA_Supplement_corollary_5_6
-- name    : ShiAuthentication.BA.Supplement.corollary_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:25:05.791202+00:00
-- url     : https://prove2.me/theorems/4467daf3-8a79-4301-beea-39369a2c542e
-- title:
--   Corollary 5.6 — equal-size receiver sets
-- statement:
--   Let $2t<n$, put $r=n-2t$, and suppose $\mathrm{BB}(G,S,t)$ is feasible on the public authentication graph $G$. Let $W\subseteq P$ contain $S$ and put $R'=P\setminus W$. If $4|W|+3r\le n$, then every pair of disjoint sets $A,B\subseteq R'$ with $|A|=|B|=k\ge r+|W|$ has a receiver $z\in R'$ satisfying
--   $$\widehat V_z\cap A\neq\emptyset\quad\text{and}\quad \widehat V_z\cap B\neq\emptyset .$$
--
--   In the bipartite graph on two copies of $R'$ formed by the bicliques $(\widehat V_z\cap R')\times(\widehat V_z\cap R')$, this excludes $k$-by-$k$ independent sets; Lemma 5.7 then converts it into an edge count (Theorem 5.4).
--
--   Differences from the source:
--   - encoding: BB(G, S, t) feasible → BBPossible .publicGraph t G S; reason: Definition 3.1 in the model of §3.1, where the authentication graph G is public
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Corollary 5.6, p. 30

import Definitions.Def_ShiAuthentication_BA_Supplement_Complexity

set_option autoImplicit false

namespace ShiAuthentication.BA.Supplement

/-- **Corollary 5.6**, p. 30. Let `2t < n`, `r = n − 2t`, and suppose `BB(G, S, t)` is feasible
(public authentication graph). For any `W ⊆ P` containing `S`, with `R' = P \ W`: if
`4|W| + 3r ≤ n`, then every pair of disjoint sets `A, B ⊆ R'` with `|A| = |B| = k ≥ r + |W|` has
a receiver `z ∈ R'` with `V̂_z ∩ A ≠ ∅` and `V̂_z ∩ B ≠ ∅`. -/
theorem corollary_5_6 (n t r : ℕ) (h2t : 2 * t < n) (hr : r = n - 2 * t) (G : AuthGraph n)
    (S : Fin n) (hBB : BBPossible .publicGraph t G S) (W : Finset (Fin n)) (hSW : S ∈ W)
    (hW : 4 * W.card + 3 * r ≤ n) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hAW : Disjoint A W) (hBW : Disjoint B W) (k : ℕ) (hAk : A.card = k) (hBk : B.card = k)
    (hk : r + W.card ≤ k) :
    ∃ z : Fin n, z ∉ W ∧ (closedVerifiers G z ∩ A).Nonempty ∧
      (closedVerifiers G z ∩ B).Nonempty := by sorry

end ShiAuthentication.BA.Supplement
