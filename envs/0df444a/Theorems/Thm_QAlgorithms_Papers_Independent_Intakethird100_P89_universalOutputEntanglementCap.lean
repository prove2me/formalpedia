-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_universalOutputEntanglementCap
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.universalOutputEntanglementCap
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:18:55.634448+00:00
-- url     : https://prove2.me/theorems/2ec94f6d-6590-46d6-b9d7-e4a90aae9a70
-- title:
--   Universal output-entanglement cap for phase-insensitive channels
-- statement:
--   Let $r\ge0$, $\tau\ge0$, and let $\Phi$ be a zero-displacement phase-insensitive Gaussian channel on a complete oscillator, with noise $y\ge|1-\tau|$. For every normalized trace-class two-oscillator input $\rho$, apply $\Phi$ to the first oscillator and the identity to the second. Partial transpose is taken in the number basis, and the trace norm has values in $[0,\infty]$. Then
--
--   $$y\ge e^{-2r}(1+\tau)\quad\Longleftrightarrow\quad\forall\rho,\ \bigl\|[(\Phi\otimes\mathrm{id})(\rho)]^\Gamma\bigr\|_1\le e^{2r}.$$
--
--   Equivalently, membership in the physical closed region defined by (3) and (8) is precisely this universal cap. At $r=0$ its scalar threshold becomes $y\ge1+\tau$, the entanglement-breaking threshold (4).
--
--   This statement tests all input densities, including non-Gaussian and infinite-energy ones. The closed region includes ideal boundary limits; it is not asserted to be the finite-energy realization set.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 3, Implementable channels and universal output-entanglement cap, Eq. (8)

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

/-- PDF p.3, (8): universal output cap on ALL normalized two-mode states,
not just Gaussian tests. Infinity of partial-transpose trace norm is preserved.
At r=0 the same condition is the entanglement-breaking noise threshold (4). -/
theorem universalOutputEntanglementCap (r tau y : ℝ) (Phi : OscillatorChannel)
    (hr : 0 ≤ r) (htau : 0 ≤ tau) (hPhi : PhaseInsensitive Phi tau y) :
    (Real.exp (-2 * r) * (1 + tau) ≤ y ↔
      ∀ rho : State (ℕ × ℕ),
        traceSize (partialTransposeFirst (tensorApply Phi rho.coefficients)) ≤
          ENNReal.ofReal (Real.exp (2 * r))) ∧
    ((tau, y) ∈ entanglementAccessibleRegion r ↔
      ∀ rho : State (ℕ × ℕ),
        traceSize (partialTransposeFirst (tensorApply Phi rho.coefficients)) ≤
          ENNReal.ofReal (Real.exp (2 * r))) ∧
    (Real.exp (-2 * (0 : ℝ)) * (1 + tau) ≤ y ↔ 1 + tau ≤ y) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
