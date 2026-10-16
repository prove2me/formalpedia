-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA43
-- name    : RiskEU.OOSUVar.eq_IA43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:12.031832+00:00
-- url     : https://prove2.me/theorems/6824b75c-e1ec-4883-ada0-6b1574244a92
-- title:
--   (IA43), p. IA35 — covariance matrix of the shrinkage portfolio ŵ*(κ) (Okhrin and Schmid 2006, Theorem 1)
-- statement:
--   Let Assumptions 1 and 2 hold for a market $(\mu,\Sigma,\gamma)$ with $\Sigma$ positive definite and $\gamma>0$, and let $\kappa\in[0,1]$. Then every coordinate of the shrinkage portfolio $\hat w^\star(\kappa)$ has a finite second moment, and its covariance matrix is
--
--   $$\mathbb V[\hat w^\star(\kappa)]=\Big(\frac{\sigma_g^2}{T-N-1}+\frac{\kappa^2}{\gamma^2}\frac{T(T-2+T\psi^2)}{(T-N)(T-N-1)(T-N-3)}\Big)\mathbf B+\frac{\kappa^2}{\gamma^2}\frac{T^2(T-N+1)}{(T-N)(T-N-1)^2(T-N-3)}\mathbf B\mu\mu^\top\mathbf B,$$
--
--   where $\sigma_g^2,\psi^2$ are given by (6)–(7) and $\mathbf B=\Sigma^{-1}(I-e w_g^\top)$ is the population matrix of (4).
--
--   This is the result of Okhrin and Schmid (2006, Theorem 1) in the notation of the paper; it yields the variance of the out-of-sample mean return (IA44).
--
--   **Formalization Note.** The matrix identity is stated entrywise with `ProbabilityTheory.covariance` of coordinates $i$ and $j$, together with `MemLp … 2` of each coordinate.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA43), p. IA35

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA43 {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i j : Fin N,
      MemLp (fun ω => M.wShrink κ (sampleData r ω) i) 2 P ∧
      covariance (fun ω => M.wShrink κ (sampleData r ω) i)
          (fun ω => M.wShrink κ (sampleData r ω) j) P =
        ((M.sigmaG2 / ((T : ℝ) - N - 1) +
              κ ^ 2 / M.gamma ^ 2 * ((T : ℝ) * ((T : ℝ) - 2 + T * M.psi2) /
                (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3)))) • M.B +
          (κ ^ 2 / M.gamma ^ 2 * ((T : ℝ) ^ 2 * ((T : ℝ) - N + 1) /
                (((T : ℝ) - N) * ((T : ℝ) - N - 1) ^ 2 * ((T : ℝ) - N - 3)))) •
            (M.B * vecMulVec M.mu M.mu * M.B)) i j := by sorry

end RiskEU.OOSUVar
