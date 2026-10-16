-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA49
-- name    : RiskEU.OOSUVar.eq_IA49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:02.941559+00:00
-- url     : https://prove2.me/theorems/623ee0ad-4ca8-455a-836f-63ef0dbc56c1
-- title:
--   (IA49), p. IA36 — expectation of the out-of-sample return variance ŵ*(κ)ᵀΣŵ*(κ)
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then the out-of-sample return variance $\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)$ is integrable and
--
--   $$\mathbb E\big[\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)\big]=\sigma_g^2\frac{T-2}{T-N-1}+\frac{\kappa^2}{\gamma^2}\frac{T(T-2)(N-1+T\psi^2)}{(T-N)(T-N-1)(T-N-3)}.$$
--
--   This first moment, due to Kan et al. (2022b), enters both the variance (IA59) and the covariance (IA68).
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA49), p. IA36

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA49 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => M.oosVar κ (sampleData r ω)) P ∧
    ∫ ω, M.oosVar κ (sampleData r ω) ∂P =
      M.sigmaG2 * (((T : ℝ) - 2) / ((T : ℝ) - N - 1)) +
        κ ^ 2 / M.gamma ^ 2 * ((T : ℝ) * ((T : ℝ) - 2) * ((N : ℝ) - 1 + T * M.psi2) /
          (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3))) := by sorry

end RiskEU.OOSUVar
