-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_optimizedTMSSGain
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.optimizedTMSSGain
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:23:36.413963+00:00
-- url     : https://prove2.me/theorems/69dad861-c8da-486e-85a0-dfd481cabf9f
-- title:
--   Globally optimized gain with a fixed pure TMSS
-- statement:
--   Let $\lambda>0$, $r\ge0$, both finite. Fix the normalized pure TMSS with covariance blocks $A=B=\cosh(2r)I$, $C=-\sinh(2r)\sigma_z$, logarithmic negativity $2r$, and finite per-mode photon number $\sinh^2r$. For every gain $g>0$ its BK map exists on every input density and is the phase-insensitive channel with
--
--   $$\tau=g^2,\qquad y=(1+g^2)\cosh(2r)-2g\sinh(2r).$$
--
--   The actual Gaussian-prior average fidelity, globally optimized over all positive gains, is attained at
--
--   $$g_{\rm opt}=\frac{2+\lambda\sinh(2r)}{2+\lambda+\lambda\cosh(2r)}>0,\qquad \overline F_{\rm TMSS}=\frac{\operatorname{sech}^2r+\lambda}{2+\lambda-2\tanh r}.$$
--
--   The attainable fidelity set has the displayed greatest element, and its independently defined supremum equals that value. The resource is fixed before the gain and before all input states.
--
--   This optimizes gain at fixed squeezing, unlike (10), which minimizes squeezing for a fixed channel.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 4, Optimized-gain fidelity with a fixed TMSS resource, Eq. (16)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.4, (16): a fixed normalized TMSS precedes the optimization over
all g>0. The closed value is globally maximal and is attained at the stated gain. -/
theorem optimizedTMSSGain (lambda r : ℝ) (hlambda : 0 < lambda) (hr : 0 ≤ r) :
    0 < tmssOptimalGain lambda r ∧
    IsGreatest (tmssValues lambda r) (tmssClosedForm lambda r) ∧
    tmssOptimum lambda r = tmssClosedForm lambda r ∧
    (∃ rho : State (ℕ × ℕ),
      rho.coefficients = tmssKernel r ∧
      CenteredResource rho (standardFormCovariance (Real.cosh (2 * r)) (Real.cosh (2 * r))
        (-Real.sinh (2 * r)) (Real.sinh (2 * r))) ∧
      traceSize (partialTransposeFirst rho.coefficients) = ENNReal.ofReal (Real.exp (2 * r)) ∧
      twoModeMeanPhotonEnergy rho = ENNReal.ofReal (Real.sinh r ^ 2) ∧ twoModeMeanPhotonEnergy rho < ⊤ ∧
      (∀ g : ℝ, 0 < g → ∃ Phi : OscillatorChannel,
        IsBK rho g Phi ∧ PhaseInsensitive Phi (g ^ 2) (tmssNoise g r) ∧
        gaussianPriorFidelity lambda Phi = phaseInsensitiveFidelityFormula lambda (g ^ 2) (tmssNoise g r)) ∧
      (∃ Phi : OscillatorChannel, IsBK rho (tmssOptimalGain lambda r) Phi ∧
        gaussianPriorFidelity lambda Phi = tmssClosedForm lambda r)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
