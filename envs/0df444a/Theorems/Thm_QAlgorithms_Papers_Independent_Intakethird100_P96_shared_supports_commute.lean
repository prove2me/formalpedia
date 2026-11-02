-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_shared_supports_commute
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.shared_supports_commute
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:31:28.310735+00:00
-- url     : https://prove2.me/theorems/5c04a19f-5d12-4096-be6a-b4331c560284
-- title:
--   Commuting subalgebras have commuting shared-factor supports
-- statement:
--   Let $B_1,B_2,B_3$ be finite-dimensional complex C*-algebras, $A_1\subseteq B_1\otimes B_2$ and $A_2\subseteq B_2\otimes B_3$ star subalgebras. Suppose $A_1\otimes1$ and $1\otimes A_2$ commute elementwise in the common three-factor algebra. Define each support algebra by generating the star algebra from all coefficient slices on the indicated factor. Then
--
--   $$[S(A_1,B_2),S(A_2,B_2)]=0.$$
--
--   This transfers commutation to the common tensor factor; no containment of the ambient identity in either subalgebra is required.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 10, Lemma 8: commutation passes to shared-factor supports

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

section SupportAlgebras

variable {B1 B2 B3 : Type*} [CStarAlgebra B1] [CStarAlgebra B2] [CStarAlgebra B3]

/-- Lemma 8, PDF p.10: supports on the common middle factor commute. -/
theorem shared_supports_commute
    [FiniteDimensional ℂ B1] [FiniteDimensional ℂ B2] [FiniteDimensional ℂ B3]
    (A1 : NonUnitalStarSubalgebra ℂ (B1 ⊗[ℂ] B2))
    (A2 : NonUnitalStarSubalgebra ℂ (B2 ⊗[ℂ] B3))
    (hcomm : ∀ a ∈ A1, ∀ b ∈ A2,
      Commute ((TensorProduct.assoc ℂ B1 B2 B3) (a ⊗ₜ[ℂ] (1 : B3)))
        ((1 : B1) ⊗ₜ[ℂ] b)) :
    ∀ x ∈ supportRight (A1 : Set (B1 ⊗[ℂ] B2)), ∀ y ∈ supportLeft (A2 : Set (B2 ⊗[ℂ] B3)), Commute x y := by sorry

end SupportAlgebras

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
