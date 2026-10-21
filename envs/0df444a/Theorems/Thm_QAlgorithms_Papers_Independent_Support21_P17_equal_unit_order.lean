-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_equal_unit_order
-- name    : QAlgorithms.Papers.Independent.Support21.P17.equal_unit_order
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:44:56.967443+00:00
-- url     : https://prove2.me/theorems/9a03b96e-8188-4592-8486-73ab5487b3ce
-- title:
--   CP maps agreeing at the identity
-- statement:
--   Let $S,T:B(H)\to B(K)$ be normal complex-linear CP maps on complex separable Hilbert spaces, with $S(I_H)=T(I_H)$. Then
--
--   $$S-T\text{ is completely positive}\iff S=T.$$
--
--   This extends channel incomparability to a common, arbitrary value at the identity. The source sentence omits the zero difference; the precise iff is the conclusion of its preceding norm argument.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 12, §4 remark: CP maps agreeing at the identity

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Section 4 remark, PDF p.12: equal values at the identity permit only a zero CP
difference. Printed: "cannot be a CP map"; changed: "CP iff S=T"; why: the zero
difference is CP, as the preceding norm argument itself shows. -/
theorem equal_unit_order (H K : SeparableHilbertSpace) (S T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T)
    (h_unit : S (ContinuousLinearMap.id ℂ H) = T (ContinuousLinearMap.id ℂ H)) :
    CompletelyDominated T S ↔ S = T := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
