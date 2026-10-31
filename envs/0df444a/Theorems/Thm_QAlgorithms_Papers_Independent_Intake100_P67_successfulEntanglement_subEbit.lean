-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_successfulEntanglement_subEbit
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.successfulEntanglement_subEbit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:31:24.994817+00:00
-- url     : https://prove2.me/theorems/d312e0b0-215b-4411-bef2-abcd42c48300
-- title:
--   Sub-ebit consumption on success and heralded swapping gain
-- statement:
--   Let $N\ge2$ and use the explicitly optimized faithful probabilistic resource (54) and its square-root postmeasurement instrument, retaining all Alice systems. For every normalized pure input and every successful port, the branch probability is positive and the normalized remaining-Bob marginal is a density matrix. Write $E_{\rm ini}$ for the entropy of the initial Bob marginal and $E_{\rm res}$ for the entropy of the unused Bob ports after the branch, both in bits. Then
--
--   $$E_{\rm ini}-E_{\rm res}<1,\qquad E_{\rm ini}<E_{\rm res}+1.$$
--
--   The first inequality is the paper's all-$N$ success-conditioned sub-ebit consumption claim. In entanglement swapping, the faithfully teleported half-pair contributes one new ebit, so the second inequality expresses a heralded increase of Alice–Bob entanglement on success.
--
--   This is neither an average LOCC gain nor a claim about arbitrary instruments with the same effects.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 9, §VIII and Fig.4, pp.9–10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.9–10, §VIII: the stated all-N sub-ebit consumption on success and consequent
heralded swapping gain. Applies to the specified optimal resource and square-root instrument,
with all Alice systems retained, not an average over success and failure. -/
theorem successfulEntanglement_subEbit (N : ℕ) (hN : 2 ≤ N)
    (v : EuclideanSpace ℂ Bool) (hv : IsState v) (i : Fin N) :
    IsDensityMatrix (bobDensity (resourceOperator (probabilisticX N))) ∧
    0 < postBranchProbability (resourceOperator (probabilisticX N)) (probabilisticMeasurement N i) v ∧
    IsDensityMatrix (residualDensity (resourceOperator (probabilisticX N))
      (probabilisticMeasurement N i) v i) ∧
    vnEntropy (bobDensity (resourceOperator (probabilisticX N))) -
      vnEntropy (residualDensity (resourceOperator (probabilisticX N))
        (probabilisticMeasurement N i) v i) < 1 ∧
    vnEntropy (bobDensity (resourceOperator (probabilisticX N))) <
      vnEntropy (residualDensity (resourceOperator (probabilisticX N))
        (probabilisticMeasurement N i) v i) + 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
