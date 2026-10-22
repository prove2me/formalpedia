-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_tensor_rationalSystem
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.tensor_rationalSystem
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:52:34.132982+00:00
-- url     : https://prove2.me/theorems/9ee532b9-e715-4be1-afde-5cede9df7ca4
-- title:
--   Proposition 2.5
-- statement:
--   Let $R$ be a commutative unital ring. Let $(P,A,b)$ and $(Q,B,c)$ be rational systems of arbitrary $R$-modules, meaning that all maps $\alpha_X$ associated with either pairing are injective. Let $d$ be the bilinear pairing on $(P\otimes_R Q)\times(A\otimes_R B)$ defined by
--
--   $$d(p\otimes q,a\otimes b)=b(p,a)c(q,b).$$
--
--   Then $(P\otimes_R Q,A\otimes_R B,d)$ is a rational system. On finite sums the displayed formula expands over both tensor-presentation indices. This supplies tensor compatibility for rationality.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 4, Proposition 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]

variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]

variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]

variable [AddCommGroup M] [Module R M]

/-- Proposition 2.5, PDF pp.4-5: tensoring rational systems. -/
theorem tensor_rationalSystem (b : P →ₗ[R] A →ₗ[R] R)
    (c : Q →ₗ[R] B →ₗ[R] R) (hb : IsRationalSystem b) (hc : IsRationalSystem c) :
    IsRationalSystem (tensorPairing b c) := by sorry

end Pairings

end QAlgorithms.Papers.Independent.Gap48.P16

end
