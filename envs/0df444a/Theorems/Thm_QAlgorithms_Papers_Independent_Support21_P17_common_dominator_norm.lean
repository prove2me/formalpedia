-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_common_dominator_norm
-- name    : QAlgorithms.Papers.Independent.Support21.P17.common_dominator_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:52:11.167279+00:00
-- url     : https://prove2.me/theorems/a6ab193c-1b63-4ace-927f-c0a3a54c4764
-- title:
--   RN norm estimate with a common dominator
-- statement:
--   Fix a normal CP map $T:B(H)\to B(K)$ and its canonical dilation $T(A)=V^*(A\otimes I_E)V$ on complex separable Hilbert spaces. If normal CP maps $T_1,T_2$ satisfy $T_i\le T$, there are positive contractions $F_i\in B(E)$ with $T_i(A)=V^*(A\otimes F_i)V$, and
--
--   $$\|T_1-T_2\|_{\rm cb}\le\|V\|\,\|(I_H\otimes(F_1-F_2))V\|\le\|V\|^2\|F_1-F_2\|.$$
--
--   If $T$ is a channel, the bound becomes $\|T_1-T_2\|_{\rm cb}\le\|F_1-F_2\|$; in particular, for $S\le T$, $\|S-T\|_{\rm cb}\le\|I_E-F\|$. This compares maps through one fixed dilation, without requiring the dominated maps to be channels.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 18, §6, unnumbered: RN norm estimate (13)

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

/-- Section 6, PDF p.18, (13): the common-dominator estimate, including the sharper
intermediate bound and its channel specializations. Amplification of F1-F2 is explicit. -/
theorem common_dominator_norm (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (T1 T2 : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hT1 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T1)
    (hT2 : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T2)
    (h1 : CompletelyDominated T1 T) (h2 : CompletelyDominated T2 T) :
    ∃ F1 F2 : HilbertEndomorphism E, PositiveContraction F1 ∧ PositiveContraction F2 ∧
      (∀ A, T1 A = compress V (completedTensorMap A F1) ∧ T2 A = compress V (completedTensorMap A F2)) ∧
      completelyBoundedNorm (T1 - T2) ≤ ‖V‖ * ‖(completedTensorMap (ContinuousLinearMap.id ℂ H) (F1 - F2)).comp V‖ ∧
      ‖V‖ * ‖(completedTensorMap (ContinuousLinearMap.id ℂ H) (F1 - F2)).comp V‖ ≤ ‖V‖ ^ 2 * ‖F1 - F2‖ ∧
      (IsUnitalNormalCP T → completelyBoundedNorm (T1 - T2) ≤ ‖F1 - F2‖) ∧
      (IsUnitalNormalCP T → T2 = T → completelyBoundedNorm (T1 - T) ≤ ‖ContinuousLinearMap.id ℂ E - F1‖) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
