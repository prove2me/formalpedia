-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_finiteDual_tensor
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.finiteDual_tensor
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:59:30.496563+00:00
-- url     : https://prove2.me/theorems/66c35099-f560-4826-8d55-3568703537c0
-- title:
--   Theorem 4.10
-- statement:
--   Let $R$ be a commutative noetherian unital ring and let $A,B$ be associative unital $R$-algebras with property $P_\ell$. The canonical $R$-linear map determined by
--
--   $$
--   \pi:A^\circ\otimes_R B^\circ\ \xrightarrow{\ \sim\ }\ (A\otimes_R B)^\circ,
--   \qquad \pi(f\otimes g)(a\otimes b)=f(a)g(b)
--   $$
--
--   is an isomorphism. In particular, its values lie in the finite dual and it is both injective and surjective. This asserts the particular evaluation map, not just existence of an unrelated equivalence, and does not assign an algebra structure to the finite duals of general algebras.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 14, Theorem 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section AlgebraOperations

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Theorem 4.10, PDF pp.14-15: canonical tensor-product duality, as an R-linear isomorphism. -/
theorem finiteDual_tensor [IsNoetherianRing R] (hA : PropertyLeft R A) (hB : PropertyLeft R B) :
    ∃ e : finiteDual R A ⊗[R] finiteDual R B ≃ₗ[R] finiteDual R (A ⊗[R] B),
      ∀ z, (e z).val = finiteDualTensorMap z := by sorry

end AlgebraOperations

end QAlgorithms.Papers.Independent.Gap48.P16

end
