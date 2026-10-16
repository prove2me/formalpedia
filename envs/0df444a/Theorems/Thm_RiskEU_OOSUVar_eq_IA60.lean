-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA60
-- name    : RiskEU.OOSUVar.eq_IA60
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:10.886063+00:00
-- url     : https://prove2.me/theorems/61aa4bd9-4504-4eb3-a3ee-ed3b3135137a
-- title:
--   (IA60), p. IA38 — expectation of the out-of-sample mean return ŵ*(κ)ᵀµ
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then $\hat w^\star(\kappa)^\top\mu$ is integrable and
--
--   $$\mathbb E\big[\hat w^\star(\kappa)^\top\mu\big]=\mu_g+\frac{\kappa}{\gamma}\frac{T\psi^2}{T-N-1}.$$
--
--   This first moment, due to Kan et al. (2022b), enters the covariance (IA68).
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA60), p. IA38

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA60 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => M.oosMean κ (sampleData r ω)) P ∧
    ∫ ω, M.oosMean κ (sampleData r ω) ∂P =
      M.muG + κ / M.gamma * ((T : ℝ) * M.psi2 / ((T : ℝ) - N - 1)) := by sorry

end RiskEU.OOSUVar
