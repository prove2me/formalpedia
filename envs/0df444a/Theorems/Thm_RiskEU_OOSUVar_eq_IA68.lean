-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA68
-- name    : RiskEU.OOSUVar.eq_IA68
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:08.371734+00:00
-- url     : https://prove2.me/theorems/bba43f48-096d-484b-b846-38245fd41feb
-- title:
--   (IA68), p. IA39 — covariance between the out-of-sample mean return and the out-of-sample return variance of ŵ*(κ)
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then $\hat w^\star(\kappa)^\top\mu$ and $\hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)$ have finite second moments and
--
--   $$\mathbb{C}\mathrm{ov}\big[\hat w^\star(\kappa)^\top\mu,\ \hat w^\star(\kappa)^\top\Sigma\hat w^\star(\kappa)\big]=\frac{2\kappa\sigma_g^2\psi^2}{\gamma}\frac{T(T-2)}{(T-N-1)^2(T-N-3)}+\frac{2\kappa^3\psi^2}{\gamma^3}\frac{T^2(T-2)(T+N-3+2T\psi^2)}{(T-N)(T-N-1)^2(T-N-3)(T-N-5)}.$$
--
--   This is the third of the three terms of the decomposition (IA42) of the out-of-sample utility variance.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA68), p. IA39

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA68 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.oosMean κ (sampleData r ω)) 2 P ∧
    MemLp (fun ω => M.oosVar κ (sampleData r ω)) 2 P ∧
    covariance (fun ω => M.oosMean κ (sampleData r ω)) (fun ω => M.oosVar κ (sampleData r ω)) P =
      2 * κ * M.sigmaG2 * M.psi2 / M.gamma *
          ((T : ℝ) * ((T : ℝ) - 2) / (((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3))) +
        2 * κ ^ 3 * M.psi2 / M.gamma ^ 3 *
          ((T : ℝ) ^ 2 * ((T : ℝ) - 2) * ((T : ℝ) + N - 3 + 2 * T * M.psi2) /
            (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5))) := by sorry

end RiskEU.OOSUVar
