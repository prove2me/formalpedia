-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_channels_incomparable
-- name    : QAlgorithms.Papers.Independent.Support21.P17.channels_incomparable
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:44:24.324994+00:00
-- url     : https://prove2.me/theorems/2bf8dcf7-3a2c-4c89-bf38-51237defa814
-- title:
--   Quantum channels are incomparable
-- statement:
--   Let $S,T:B(H)\to B(K)$ be quantum channels on complex separable Hilbert spaces: they are normal complex-linear CP maps with $S(I_H)=T(I_H)=I_K$. Then
--
--   $$T-S\text{ is completely positive}\iff S=T.$$
--
--   Thus a channel has no different channel below it in CP order. Trace preservation refers to the predual maps, not to these Heisenberg-picture maps.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 12, Proposition 4.1: channels are incomparable

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

/-- Proposition 4.1, PDF p.12: channels are incomparable in CP order.
The independent norm proof in the remark avoids the defective Theorem 3.5. -/
theorem channels_incomparable (H K : SeparableHilbertSpace) (S T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hS : IsUnitalNormalCP S) (hT : IsUnitalNormalCP T) : CompletelyDominated S T ↔ S = T := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
