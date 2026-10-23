-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_at_inv_kappa
-- name    : ProjSelfConcordant.ConicExt.pmu_at_inv_kappa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:13.455031+00:00
-- url     : https://prove2.me/theorems/5cfc06ff-03e1-41df-a04a-18c9543781d3
-- title:
--   §2, p. 5 — the values p_μ(∓κ⁻¹) factor as products of two linear terms in μ
-- statement:
--   Let $\kappa\ge1$, $\mu\in\mathbb R$, and $\nu=\kappa^2+1$. Then
--   $$p_\mu(-\kappa^{-1})=\Bigl(\frac{2(\kappa^4+5\kappa^2+2)}{\kappa^3}+\mu\Bigr)\Bigl(\frac{2(\kappa^2-1)}{\kappa}-\mu\Bigr),\qquad p_\mu(\kappa^{-1})=\Bigl(\frac{2(\kappa^4+5\kappa^2+2)}{\kappa^3}-\mu\Bigr)\Bigl(\frac{2(\kappa^2-1)}{\kappa}+\mu\Bigr).$$
--
--   Evaluating the sextic at the two points $\mp\kappa^{-1}$ isolates the bound $|\mu|\le 2(\kappa^2-1)/\kappa$.
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 (display for p_µ(−κ⁻¹), p_µ(κ⁻¹))

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: for `ν = κ² + 1`, `κ ≥ 1`,
`p_μ(−κ⁻¹) = (2(κ⁴ + 5κ² + 2)/κ³ + μ)(2(κ² − 1)/κ − μ)` and
`p_μ(κ⁻¹) = (2(κ⁴ + 5κ² + 2)/κ³ − μ)(2(κ² − 1)/κ + μ)`. -/
theorem pmu_at_inv_kappa (κ μ : ℝ) (hκ : 1 ≤ κ) :
    pmu (κ ^ 2 + 1) μ (-κ⁻¹)
        = (2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 + μ) * (2 * (κ ^ 2 - 1) / κ - μ) ∧
      pmu (κ ^ 2 + 1) μ κ⁻¹
        = (2 * (κ ^ 4 + 5 * κ ^ 2 + 2) / κ ^ 3 - μ) * (2 * (κ ^ 2 - 1) / κ + μ) := by sorry

end ProjSelfConcordant.ConicExt
