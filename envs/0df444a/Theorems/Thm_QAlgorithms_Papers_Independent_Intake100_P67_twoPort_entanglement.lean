-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_twoPort_entanglement
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.twoPort_entanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:30:39.050891+00:00
-- url     : https://prove2.me/theorems/586d36f8-d679-4362-adb1-21acdabc238d
-- title:
--   Exact two-port initial and residual entanglement
-- statement:
--   Use the optimal two-port resource and the square-root instrument of §VII. Entropy is measured in bits. The initial Bob marginal is a density matrix and its entropy is exactly
--
--   $$E_{\rm ini}=-\frac1{10}\log_2\frac1{10}-\frac9{10}\log_2\frac3{10}.$$
--
--   For either successful port and every normalized pure input, the branch probability is positive, the normalized unused-port marginal is a density matrix, and its entropy, equal to the entanglement of the pure residual across $(AC):B_{\rm unused}$, is
--
--   $$E_{\rm res}=1,\qquad E_{\rm ini}-E_{\rm res}<1.$$
--
--   The selected output port is excluded from this residual. The source's decimal values $1.90$ and $0.90$ are rounded; they are not exact equalities.
--
--   This gives an exact sub-ebit consumption example.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 9, §VIII, pp.9–10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.9–10, §VIII: exact two-port entropies and consumption below one ebit.
Printed E_ini=1.90 and consumption=0.90 are rounded; the exact initial entropy is used. -/
theorem twoPort_entanglement :
    IsDensityMatrix (bobDensity (resourceOperator (probabilisticX 2))) ∧
    vnEntropy (bobDensity (resourceOperator (probabilisticX 2))) = twoPortInitialEntropy ∧
    (∀ (v : EuclideanSpace ℂ Bool), IsState v → ∀ i : Fin 2,
      0 < postBranchProbability (resourceOperator (probabilisticX 2)) (twoPortMeasurement i) v ∧
      IsDensityMatrix (residualDensity (resourceOperator (probabilisticX 2))
        (twoPortMeasurement i) v i) ∧
      vnEntropy (residualDensity (resourceOperator (probabilisticX 2))
        (twoPortMeasurement i) v i) = 1) ∧
    twoPortInitialEntropy - 1 < 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
