-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_alternating_tensor_identity_two_by_two
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.alternating_tensor_identity_two_by_two
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:51:03.017364+00:00
-- url     : https://prove2.me/theorems/390e5fa7-6a9a-4013-8f91-582a69b1c125
-- title:
--   Example 23: alternating tensor identity for 2×2 matrices
-- statement:
--   For arbitrary complex $2\times2$ matrices $X_1,X_2,X_3,X_4$,
--
--   $$\sum_{\pi\in S_4}\operatorname{sgn}(\pi)\,(X_{\pi(1)}X_{\pi(2)})\otimes(X_{\pi(3)}X_{\pi(4)})=0_{4\times4}.$$
--
--   The tensor factors retain the displayed multiplication order. The identity does not assume Hermiticity, tracelessness, or a factorization into individual polynomial identities.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 19, Example 23: alternating tensor identity for 2×2 matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Example 23, Eq.86 (PDF p.19). The sum is zero as an operator on C²⊗C²,
for all complex 2×2 inputs; none are required Hermitian or traceless. -/
theorem alternating_tensor_identity_two_by_two (X : Fin 4 → (Matrix (Fin 2) (Fin 2) ℂ)) :
    (∑ pi : Equiv.Perm (Fin 4), (((Equiv.Perm.sign pi : ℤˣ) : ℤ) : ℂ) •
      Matrix.kronecker (X (pi 0)*X (pi 1)) (X (pi 2)*X (pi 3))) = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
