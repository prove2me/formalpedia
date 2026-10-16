-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA44
-- name    : RiskEU.OOSUVar.eq_IA44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:07.876038+00:00
-- url     : https://prove2.me/theorems/0bb7d583-dbcb-4b2e-b259-a94cf6a34089
-- title:
--   (IA44), p. IA35 — variance of the out-of-sample mean return ŵ*(κ)ᵀµ
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then the out-of-sample mean return $\hat w^\star(\kappa)^\top\mu$ of the shrinkage portfolio has a finite second moment and
--
--   $$\mathbb V\big[\hat w^\star(\kappa)^\top\mu\big]=\frac{\sigma_g^2\psi^2}{T-N-1}+\frac{\kappa^2\psi^2}{\gamma^2}\frac{2T(N+1)+T^2(T-N-3+2(T-N)\psi^2)}{(T-N)(T-N-1)^2(T-N-3)}.$$
--
--   This is the first of the three terms of the decomposition (IA42) of the out-of-sample utility variance.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA44), p. IA35

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA44 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.oosMean κ (sampleData r ω)) 2 P ∧
    variance (fun ω => M.oosMean κ (sampleData r ω)) P =
      M.sigmaG2 * M.psi2 / ((T : ℝ) - N - 1) +
        κ ^ 2 * M.psi2 / M.gamma ^ 2 *
          ((2 * (T : ℝ) * (N + 1) + (T : ℝ) ^ 2 * ((T : ℝ) - N - 3 + 2 * ((T : ℝ) - N) * M.psi2)) /
            (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3))) := by sorry

end RiskEU.OOSUVar
