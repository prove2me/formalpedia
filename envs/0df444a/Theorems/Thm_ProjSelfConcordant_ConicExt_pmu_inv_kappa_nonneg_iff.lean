-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_inv_kappa_nonneg_iff
-- name    : ProjSelfConcordant.ConicExt.pmu_inv_kappa_nonneg_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:00.900023+00:00
-- url     : https://prove2.me/theorems/5c02c1db-f829-4316-bd01-7b0bc0257e4c
-- title:
--   §2, p. 5 — p_μ(±κ⁻¹) ≥ 0 iff |μ| ≤ 2(κ² − 1)/κ = 2γ
-- statement:
--   Let $\kappa\ge1$, $\mu\in\mathbb R$, and $\nu=\kappa^2+1$. Then both values $p_\mu(-\kappa^{-1})$ and $p_\mu(\kappa^{-1})$ are nonnegative if and only if
--   $$|\mu|\le\frac{2(\kappa^2-1)}{\kappa},$$
--   and moreover
--   $$\frac{2(\kappa^2-1)}{\kappa}=2\,\frac{\nu-2}{\sqrt{\nu-1}}=2\gamma.$$
--
--   This gives the necessity half of the sharp constant: nonnegativity of the sextic forces condition (3) of Definition 1.4 with $\gamma=(\nu-2)/\sqrt{\nu-1}$.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 ('For κ ≥ 1 we have …')

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: for `ν = κ² + 1`, `κ ≥ 1`, both values `p_μ(±κ⁻¹)` are nonnegative if and only if
`|μ| ≤ 2(κ² − 1)/κ`, and `2(κ² − 1)/κ = 2(ν − 2)/√(ν − 1) = 2γ`. -/
theorem pmu_inv_kappa_nonneg_iff (κ μ : ℝ) (hκ : 1 ≤ κ) :
    ((0 ≤ pmu (κ ^ 2 + 1) μ (-κ⁻¹) ∧ 0 ≤ pmu (κ ^ 2 + 1) μ κ⁻¹) ↔ |μ| ≤ 2 * (κ ^ 2 - 1) / κ) ∧
      2 * (κ ^ 2 - 1) / κ = 2 * (((κ ^ 2 + 1) - 2) / Real.sqrt ((κ ^ 2 + 1) - 1)) := by sorry

end ProjSelfConcordant.ConicExt
