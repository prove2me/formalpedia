-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA59
-- name    : RiskEU.OOSUVar.eq_IA59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:09.395214+00:00
-- url     : https://prove2.me/theorems/5b5f3c10-f35b-449c-b7ea-86864efdba00
-- title:
--   (IA59), pp. IA37–IA38 — variance of the out-of-sample return variance ŵ*(κ)ᵀΣŵ*(κ)
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then $\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)$ has a finite second moment and
--
--   $$\mathbb V\big[\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)\big]=2\sigma_g^4\frac{(N-1)(T-2)}{(T-N-1)^2(T-N-3)}+\frac{4\kappa^2\sigma_g^2}{\gamma^2}\frac{T(T-2)(T+N-3)(T\psi^2+N-1)}{(T-N)(T-N-1)^2(T-N-3)(T-N-5)}+\frac{2\kappa^4}{\gamma^4}\frac{T^2(T-2)C(T,N,\psi^2)}{(T-N)^2(T-N-1)^2(T-N-2)(T-N-3)^2(T-N-5)(T-N-7)},$$
--
--   where $C(T,N,\psi^2)$ is the polynomial defined in Proposition 1.
--
--   This is the second of the three terms of the decomposition (IA42) of the out-of-sample utility variance.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA59), pp. IA37–IA38

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA59 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.oosVar κ (sampleData r ω)) 2 P ∧
    variance (fun ω => M.oosVar κ (sampleData r ω)) P =
      2 * M.sigmaG2 ^ 2 * (((N : ℝ) - 1) * ((T : ℝ) - 2) /
          (((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3))) +
        4 * κ ^ 2 * M.sigmaG2 / M.gamma ^ 2 *
          ((T : ℝ) * ((T : ℝ) - 2) * ((T : ℝ) + N - 3) * ((T : ℝ) * M.psi2 + N - 1) /
            (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5))) +
        2 * κ ^ 4 / M.gamma ^ 4 *
          ((T : ℝ) ^ 2 * ((T : ℝ) - 2) * C T N M.psi2 /
            (((T : ℝ) - N) ^ 2 * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 2) * ((T : ℝ) - N - 3) ^ 2 *
              ((T : ℝ) - N - 5) * ((T : ℝ) - N - 7))) := by sorry

end RiskEU.OOSUVar
