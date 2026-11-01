-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_minimumTMSSSqueezing
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.minimumTMSSSqueezing
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:20:55.167931+00:00
-- url     : https://prove2.me/theorems/19bd18fb-dc70-40f7-8497-99e4f1c2382b
-- title:
--   Minimum nonnegative TMSS squeezing, with singular cases corrected
-- statement:
--   Let $\tau>0$, $|1-\tau|\le y\le1+\tau$, and $(\tau,y)\ne(1,0)$. Define $r_0$ independently as the infimum of nonnegative solutions $s$ to the actual TMSS noise equation
--
--   $$(1+\tau)\cosh(2s)-2\sqrt\tau\sinh(2s)=y.$$
--
--   This set has a least element, and
--
--   $$r_0=\begin{cases}\dfrac12\operatorname{arcosh}\!\left(\dfrac{y(1+\tau)-2\sqrt{\tau[y^2-(1-\tau)^2]}}{(1-\tau)^2}\right),&\tau\ne1,\\[4pt]\dfrac12\log(2/y),&\tau=1.\end{cases}$$
--
--   A normalized pure TMSS of parameter $r_0$, with covariance blocks $A=B=\cosh(2r_0)I$, $C=-\sinh(2r_0)\sigma_z$, has logarithmic negativity $2r_0$ and finite per-mode photon number $\sinh^2 r_0$. At gain $\sqrt\tau$ it simulates this channel on every input density. The identity has no finite nonnegative solution of the noise equation. On $y=e^{-2r}(1+\tau)$, $r\ge0$, one has $r_0\ge r$, with equality exactly when $\tau=1$ or $r=0$, and strict inequality for $r>0$, $\tau\ne1$.
--
--   The unit-transmissivity extension and equality exceptions correct the printed singular formula and blanket strict comparison; no assertion of two distinct nonnegative roots is made.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 3, Minimum TMSS squeezing for the non-entanglement-breaking range, Eq. (10)

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

/-- PDF p.3, (10): minimum defined by the actual noise equation; finite
TMSS realization on every input. CORRECTIONS: tau=1 uses log(2/y)/2;
identity has no finite solution; the strict r0>r comparison has equality
at tau=1 or r=0. No assertion of two distinct nonnegative roots is made. -/
theorem minimumTMSSSqueezing (tau y : ℝ) (htau : 0 < tau)
    (hy : |1 - tau| ≤ y) (hyupper : y ≤ 1 + tau)
    (hidentity : tau ≠ 1 ∨ y ≠ 0) :
    IsLeast {s : ℝ | 0 ≤ s ∧ tmssNoise (Real.sqrt tau) s = y}
      (minimumSqueezing tau y) ∧
    minimumSqueezing tau y = squeezingClosedForm tau y ∧
    (∃ (rho : State (ℕ × ℕ)) (Phi : OscillatorChannel),
      rho.coefficients = tmssKernel (minimumSqueezing tau y) ∧
      CenteredResource rho (standardFormCovariance
        (Real.cosh (2 * minimumSqueezing tau y)) (Real.cosh (2 * minimumSqueezing tau y))
        (-Real.sinh (2 * minimumSqueezing tau y)) (Real.sinh (2 * minimumSqueezing tau y))) ∧
      twoModeMeanPhotonEnergy rho = ENNReal.ofReal (Real.sinh (minimumSqueezing tau y) ^ 2) ∧
      twoModeMeanPhotonEnergy rho < ⊤ ∧
      traceSize (partialTransposeFirst rho.coefficients) =
        ENNReal.ofReal (Real.exp (2 * minimumSqueezing tau y)) ∧
      IsBK rho (Real.sqrt tau) Phi ∧ PhaseInsensitive Phi tau y) ∧
    (¬ ∃ s : ℝ, 0 ≤ s ∧ tmssNoise 1 s = 0) ∧
    (∀ r : ℝ, 0 ≤ r → y = Real.exp (-2 * r) * (1 + tau) →
      r ≤ minimumSqueezing tau y ∧
      (minimumSqueezing tau y = r ↔ tau = 1 ∨ r = 0) ∧
      (0 < r → tau ≠ 1 → r < minimumSqueezing tau y)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
