-- Prove2me | Theorems.Thm_RankRobustAssort_proposition_2
-- name    : RankRobustAssort.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:25.426991+00:00
-- url     : https://prove2.me/theorems/b5c2570d-f5e3-435d-b9d3-e4f309140ede
-- title:
--   Proposition 2 — adding a dominating product never decreases $\rho_{i_1\cdots i_M}$
-- statement:
--   Let $S\in\mathcal S$ and $i\notin S$. If there exists $i^*\in S$ with $r_{i^*}<r_i$ and $\mathcal M_{i^*}\subseteq\mathcal M_i$, then
--
--   $$
--   \rho_{i_1\cdots i_M}(S)\le\rho_{i_1\cdots i_M}(S\cup\{i\})\qquad\text{for each }(i_1,\dots,i_M)\in\mathcal L.
--   $$
--
--   Together with Proposition 1, whose constraints do not depend on the assortment, this shows that adding such a product never lowers the worst-case expected revenue.
--
--   Differences from the source:
--   - encoding: minima of revenues over finite index sets → minima in $\mathbb R\cup\{+\infty\}$; reason: the index sets are nonempty for $S\in\mathcal S$ and tuples in $\mathcal L$, so the values are the paper's real minima
--   - generalization: the paper's standing assumption $\mathcal U\ne\emptyset$ (p.8) → not assumed; reason: the statement involves only rankings, tuples, $\mathcal L$, $\rho$ and the graph $\mathcal G$, none of which depends on the data $v$ or the radius $\eta$, so it is stated for every instance; on instances with $\mathcal U\ne\emptyset$ it is exactly the paper's statement
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Proposition 2, p.16

import Mathlib
import Definitions.Def_RankRobustAssort_InL
import Definitions.Def_RankRobustAssort_rho
import Definitions.Def_RankRobustAssort_Mset

namespace RankRobustAssort

/-- **Proposition 2.** Let `S ∈ 𝒮` and `i ∉ S`. If there exists `i* ∈ S` that satisfies
`r_{i*} < r_i` and `ℳ_{i*} ⊆ ℳ_i`, then `ρ_{i₁⋯i_M}(S) ≤ ρ_{i₁⋯i_M}(S ∪ {i})` for each
`(i₁,…,i_M) ∈ ℒ`.

Sturt, arXiv:2112.05010v4, Proposition 2, p.16.

Formalization Note: `S ∈ 𝒮` is `0 ∈ S`, `S ∪ {i}` is `insert i S`, and `ρ` takes values in
`WithTop ℝ` (finite on `ℒ` for `S ∋ 0`). -/
theorem proposition_2 {n M : ℕ} (P : Problem n M) (S : Finset (Fin (n + 1))) (hS : 0 ∈ S)
    (i : Fin (n + 1)) (hi : i ∉ S)
    (hdom : ∃ i' ∈ S, P.r i' < P.r i ∧ Mset P i' ⊆ Mset P i) :
    ∀ t : Fin M → Fin (n + 1), InL P t → rho P t S ≤ rho P t (insert i S) := by sorry

end RankRobustAssort
