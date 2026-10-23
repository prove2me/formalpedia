-- Prove2me | Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_pm_factorization
-- name    : ProjSelfConcordant.ConicExt.pmu_pm_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:16.367711+00:00
-- url     : https://prove2.me/theorems/f6893e49-3660-4642-aeb1-0377a686d002
-- title:
--   §2, p. 5 — factorizations of p_{μ±}(t), μ± = ±2γ, and their nonnegativity for κ ≥ 1
-- statement:
--   Let $\kappa\ge1$, $\nu=\kappa^2+1$, $\gamma=(\nu-2)/\sqrt{\nu-1}$, so that $\mu_\pm=\pm2\gamma=\pm2(\kappa^2-1)/\kappa$. Then for every real $t$
--   $$p_{\mu_+}(t)=4\kappa^{-2}(\kappa t+1)^2\bigl(\kappa(t^2+2)(t-1)^2+(\kappa-1)((t^4+3t^2+3)\kappa+1)\bigr),$$
--   $$p_{\mu_-}(t)=4\kappa^{-2}(\kappa t-1)^2\bigl(\kappa(t^2+2)(t+1)^2+(\kappa-1)((t^4+3t^2+3)\kappa+1)\bigr),$$
--   and both values are nonnegative.
--
--   These factorizations certify that the sextic is nonnegative at the extreme admissible values $\mu=\pm2\gamma$, the sufficiency half of the sharp constant.
--
--   **Formalization Note** $\mu_\pm$ is written directly as $\pm2(\kappa^2-1)/\kappa$, which equals $\pm2\gamma$ for $\kappa\ge1$ (that equality is part of the companion statement `pmu_inv_kappa_nonneg_iff`).
-- source:
--   Hildebrand, Projectively Self-Concordant Barriers, arXiv:1909.01883v2, p. 5, §2, proof of Theorem 1.5 (display for p_µ+(t), p_µ−(t))

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting

namespace ProjSelfConcordant.ConicExt

/-- §2, p. 5: for `ν = κ² + 1`, `κ ≥ 1` and `μ± = ±2γ = ±2(κ² − 1)/κ`,
`p_{μ+}(t) = 4κ⁻²(κt + 1)²(κ(t² + 2)(t − 1)² + (κ − 1)((t⁴ + 3t² + 3)κ + 1))`,
`p_{μ−}(t) = 4κ⁻²(κt − 1)²(κ(t² + 2)(t + 1)² + (κ − 1)((t⁴ + 3t² + 3)κ + 1))`,
and both polynomials are nonnegative. -/
theorem pmu_pm_factorization (κ t : ℝ) (hκ : 1 ≤ κ) :
    pmu (κ ^ 2 + 1) (2 * (κ ^ 2 - 1) / κ) t
        = 4 * κ⁻¹ ^ 2 * (κ * t + 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t - 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) ∧
      pmu (κ ^ 2 + 1) (-(2 * (κ ^ 2 - 1) / κ)) t
        = 4 * κ⁻¹ ^ 2 * (κ * t - 1) ^ 2
          * (κ * (t ^ 2 + 2) * (t + 1) ^ 2 + (κ - 1) * ((t ^ 4 + 3 * t ^ 2 + 3) * κ + 1)) ∧
      0 ≤ pmu (κ ^ 2 + 1) (2 * (κ ^ 2 - 1) / κ) t ∧
      0 ≤ pmu (κ ^ 2 + 1) (-(2 * (κ ^ 2 - 1) / κ)) t := by sorry

end ProjSelfConcordant.ConicExt
