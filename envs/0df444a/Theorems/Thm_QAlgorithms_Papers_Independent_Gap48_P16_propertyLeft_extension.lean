-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_propertyLeft_extension
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.propertyLeft_extension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:58:06.096235+00:00
-- url     : https://prove2.me/theorems/1a228911-8700-4cb9-b074-664d044623ee
-- title:
--   Proposition 4.6
-- statement:
--   Let $R$ be a commutative noetherian unital ring. Let $A,B$ be associative unital $R$-algebras, let $i:A\hookrightarrow B$ be an injective unital $R$-algebra map, and assume $A$ has property $P_\ell$. Give $B$ the right $A$-action $b\cdot a=b\,i(a)$. Then
--
--   $$B\text{ finite projective as a right }A\text{-module}\quad\Longrightarrow\quad P_\ell(B).$$
--
--   The module structure is restricted along the stated inclusion; no unrelated right action is admitted. This is a closure result for the left-ideal approximation property.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 13, Proposition 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section AlgebraOperations

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Proposition 4.6, PDF p.13: closure under finite projective RIGHT extensions. -/
theorem propertyLeft_extension [IsNoetherianRing R] (hA : PropertyLeft R A)
    (f : A →ₐ[R] B) (hf : Function.Injective f) (hB : IsFiniteProjectiveRightExtension f) :
    PropertyLeft R B := by sorry

end AlgebraOperations

end QAlgorithms.Papers.Independent.Gap48.P16

end
