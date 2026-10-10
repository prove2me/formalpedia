-- Prove2me | Theorems.Thm_TailRiskSharing_RobustVaR_display41_level_scaling
-- name    : TailRiskSharing.RobustVaR.display41_level_scaling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:02:16.701985+00:00
-- url     : https://prove2.me/theorems/e14e204b-d583-4c06-a6e8-66d2ccd2c72a
-- title:
--   (41), p. 33 — [VaR^Λ_α]¹_δ ≥ [VaR^Λ_{λα}]¹_{λδ} for λ ≥ 1
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be atomless, $\Lambda\in\{L,R\}$, $\alpha>0$, $\delta>0$ and $\lambda\ge1$ with $\lambda\alpha<1$. Write $[\rho]^1_\delta$ for the robust version of $\rho$ over the order-$1$ Wasserstein ball of radius $\delta$. For every $Y\in L^\infty$,
--
--   $$
--   [\mathrm{VaR}^\Lambda_\alpha]^1_\delta(Y)\ge[\mathrm{VaR}^\Lambda_{\lambda\alpha}]^1_{\lambda\delta}(Y).
--   $$
--
--   Scaling the level and the radius by the same factor $\lambda\ge1$ can only decrease the robust VaR. This is what reduces part (ii) of Theorem 6 (common radius, different levels) to part (i) (common level, different radii).
--
--   **Formalization Note** The paper states (41) for $\lambda\ge1$; the condition $\lambda\alpha<1$ is implicit, since VaR levels lie in $(0,1)$ throughout. It implies $\alpha<1$.
-- source:
--   Liu, Mao, Wang & Wei, Inf-convolution, Optimal Allocations, and Model Uncertainty for Tail Risk Measures, SSRN 3490348 (version of January 16, 2022), p. 33, proof of Theorem 6(ii), display (41)

import Mathlib
import Definitions.Def_TailRiskSharing_RobustVaR_Setting
import Definitions.Def_TailRiskSharing_RobustVaR_Wasserstein

namespace TailRiskSharing.RobustVaR

open MeasureTheory

theorem display41_level_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
    (Λ : TailRiskSharing.VaRConv.Side) (α δ lam : ℝ) (hα0 : 0 < α) (hδ : 0 < δ) (hlam : 1 ≤ lam) (hlamα : lam * α < 1)
    (Y : Ω → ℝ) (hY : Y ∈ TailRiskSharing.TailConv.Linf P) :
    robust P 1 (lam * δ) (TailRiskSharing.VaRConv.VaRS P Λ (lam * α)) Y ≤ robust P 1 δ (TailRiskSharing.VaRConv.VaRS P Λ α) Y := by sorry

end TailRiskSharing.RobustVaR
