-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_finiteEnergyOptimalResources
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.finiteEnergyOptimalResources
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:19:35.196381+00:00
-- url     : https://prove2.me/theorems/25d11ac6-2452-463c-8211-8736c2bd619f
-- title:
--   Finite-energy minimum-entanglement resource family
-- statement:
--   Let $r\ge0$, $\tau>0$ and $D=\tau+1-e^{2r}|\tau-1|>0$. For $r>0$ this denominator condition is equivalent to $\tanh r<\tau<1/\tanh r$. Define
--
--   $$b_{\min}=\frac{e^{2r}\tau+e^{-2r}-|\tau-1|}{D},\qquad a=\frac{b+e^{-2r}(\tau-1)}{\tau},\qquad c=\frac{b-e^{-2r}}{\sqrt\tau}.$$
--
--   For every $b\ge b_{\min}$, the symmetric covariance with blocks $A=aI$, $B=bI$, $C=-c\sigma_z$ is physical and is the doubled covariance of a normalized centered Gaussian density $\rho$ on the complete two-oscillator space. It satisfies
--
--   $$\|\rho^\Gamma\|_1=e^{2r},\qquad \overline n_{AB}=\frac{a+b-2}{4}<\infty.$$
--
--   The deterministic BK protocol at gain $\sqrt\tau$ exactly simulates, on every input density, the phase-insensitive channel with noise $e^{-2r}(1+\tau)$. Among this displayed family the per-mode mean photon number is minimized at $b=b_{\min}$. Any finite-energy Gaussian BK realization of that channel with logarithmic negativity $2s$, $s\ge0$, has $s\ge r$.
--
--   Physicality, state existence and exact simulation are conclusions of the result. The energy minimum is within family (9), with no claim of global energy optimality over all Gaussian resources.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 3, Finite-energy minimum-entanglement Gaussian resource family, Eq. (9)

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

/-- PDF p.3, (9): existence, physicality, exact all-input simulation and
minimum entanglement are CONCLUSIONS for the constructed finite-energy family.
The b=b_min energy minimum is only within the displayed family. -/
theorem finiteEnergyOptimalResources (r tau : ℝ) (hr : 0 ≤ r) (htau : 0 < tau)
    (hden : 0 < familyDenominator r tau) :
    (0 < r → (0 < familyDenominator r tau ↔
      Real.tanh r < tau ∧ tau < (Real.tanh r)⁻¹)) ∧
    (∀ b : ℝ, familyMinB r tau ≤ b →
      let a := familyA r tau b
      let c := familyC r tau b
      let V := standardFormCovariance a b (-c) c
      PhysicalCovariance V ∧
      ∃ (rho : State (ℕ × ℕ)) (Phi : OscillatorChannel),
        CenteredResource rho V ∧ twoModeMeanPhotonEnergy rho < ⊤ ∧
        twoModeMeanPhotonEnergy rho = ENNReal.ofReal ((a + b - 2) / 4) ∧
        traceSize (partialTransposeFirst rho.coefficients) = ENNReal.ofReal (Real.exp (2 * r)) ∧
        IsBK rho (Real.sqrt tau) Phi ∧
        PhaseInsensitive Phi tau (Real.exp (-2 * r) * (1 + tau))) ∧
    (∀ b : ℝ, familyMinB r tau ≤ b →
      familyMinEnergy r tau ≤ familyEnergy r tau b) ∧
    FiniteBKSimulates r tau (Real.exp (-2 * r) * (1 + tau)) ∧
    (∀ s : ℝ, 0 ≤ s → FiniteBKSimulates s tau (Real.exp (-2 * r) * (1 + tau)) → r ≤ s) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
