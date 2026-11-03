-- Prove2me | Theorems.Thm_RankRobustAssort_lemma_EC_2
-- name    : RankRobustAssort.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:36.666292+00:00
-- url     : https://prove2.me/theorems/4875ba78-89b6-4c2c-bf28-719a7576ad9c
-- title:
--   Lemma EC.2 — only the vertices $i_1,\dots,i_M$ are reachable in $\mathcal G_{i_1\cdots i_M}$
-- statement:
--   Let $(i_1,\dots,i_M)\in\mathcal L$ and $i,j\in\mathcal N_0$. If $j\prec_{i_1\cdots i_M} i$, then there exists a past assortment $m\in\mathcal M$ with
--
--   $$
--   j=i_m.
--   $$
--
--   Differences from the source:
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.2, p.ec15

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_Reach

namespace RankRobustAssort

/-- **Lemma EC.2.** Let `(i₁,…,i_M) ∈ ℒ` and `i, j ∈ 𝒩₀`. If `j ≺_{i₁⋯i_M} i`, then there exists
a past assortment `m ∈ ℳ` that satisfies `j = i_m`.

Sturt, arXiv:2112.05010v4, Lemma EC.2, p.ec15.

Formalization Note: `j ≺ i` is `Reach P t j i` (a path of at least one edge from `i` to `j`). -/
theorem lemma_EC_2 {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (ht : InL P t)
    (i j : Fin (n + 1)) (h : Reach P t j i) :
    ∃ m, j = t m := by sorry

end RankRobustAssort
