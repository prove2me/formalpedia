-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_common_dilation_norm
-- name    : QAlgorithms.Papers.Independent.Support21.P17.common_dilation_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:53:18.064818+00:00
-- url     : https://prove2.me/theorems/d850c1fd-4542-42ed-8f49-6e10d2b3c619
-- title:
--   Universal common-dilation norm estimate
-- statement:
--   Let $T_1,T_2:B(H)\to B(K)$ be normal CP maps on complex separable Hilbert spaces. Suppose arbitrary bounded operators $V_i:K\to H\otimes E$ give $T_i(A)=V_i^*(A\otimes I_E)V_i$ on one common environment. Then
--
--   $$\|T_1-T_2\|_{\rm cb}\le(\|V_1\|+\|V_2\|)\|V_1-V_2\|.$$
--
--   If both maps are channels, the right side can be replaced by $2\|V_1-V_2\|$. The estimate holds for every such pair of dilations, with no minimality, domination, or finite-dimensionality assumption.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 18, §6, unnumbered: common dilation norm estimate (14)

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

/-- Section 6, PDF p.18, (14): every common dilation gives the bound; no minimality,
CP order, unitality, or finite dimensionality is assumed for the general inequality. -/
theorem common_dilation_norm (H K E : SeparableHilbertSpace) (T1 T2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hT1 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T1)
    (hT2 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T2)
    (V1 V2 : K →L[ℂ] NoiseSpace H E)
    (hV1 : ∀ A, T1 A = compress V1 (completedTensorMap A (ContinuousLinearMap.id ℂ E)))
    (hV2 : ∀ A, T2 A = compress V2 (completedTensorMap A (ContinuousLinearMap.id ℂ E))) :
    completelyBoundedNorm (T1 - T2) ≤ (‖V1‖ + ‖V2‖) * ‖V1 - V2‖ ∧
      (IsUnitalNormalCP T1 → IsUnitalNormalCP T2 → completelyBoundedNorm (T1 - T2) ≤ 2 * ‖V1 - V2‖) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
