-- Prove2me | Theorems.Thm_PLCMarkets_ExactCover_claim_8_7_coverSet_disjoint
-- name    : PLCMarkets.ExactCover.claim_8_7_coverSet_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:12:29.754796+00:00
-- url     : https://prove2.me/theorems/2ebefb9e-5d5d-4aaf-9843-8160591b5a81
-- title:
--   CLAIM 8.7 — in an $n^{-5}$-equilibrium of $D(\mathcal C)$, the sets in $S$ are disjoint
-- statement:
--   Let $n>35$ be a multiple of $3$ and let $\mathcal C=(C_1,\dots,C_n)$ be a family of $3$-element subsets of $X=\{x_1,\dots,x_n\}$ whose union is $X$. Let $p$ be an $n^{-5}$-approximate market equilibrium of the Arrow–Debreu market $D(\mathcal C)$, let $p_m=\min_j p(j)$, and let $S$ be the set of indices $i$ with $p(C_i)\ge p_m+\tfrac16\sum_{x_j\in C_i}p(x_j)$. Then the sets indexed by $S$ are pairwise disjoint:
--
--   $$
--   i,k\in S,\ i\neq k\ \Longrightarrow\ C_i\cap C_k=\emptyset .
--   $$
--
--   The proof of Lemma 8.3 concludes by showing that these disjoint sets cover $X$.
--
--   **Formalization Note.** Disjointness is by index: if the family repeats a set, two indices of $S$ carrying the same set count as two sets of $S$.
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:22, CLAIM 8.7 (in the proof of LEMMA 8.3)

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_X3C
import Definitions.Def_PLCMarkets_ExactCover_MarketD

namespace PLCMarkets.ExactCover

theorem claim_8_7_coverSet_disjoint (n : ℕ) (C : Fin n → Finset (Fin n))
    (hcard : ∀ i, (C i).card = 3) (hdiv : 3 ∣ n) (hn : 35 < n)
    (hcover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (p : Good n → ℝ)
    (hp : (marketD C).IsApproxEquilibrium (((n : ℝ) ^ 5)⁻¹) p) :
    ∀ i ∈ coverSet C p, ∀ k ∈ coverSet C p, i ≠ k → Disjoint (C i) (C k) := by sorry

end PLCMarkets.ExactCover
