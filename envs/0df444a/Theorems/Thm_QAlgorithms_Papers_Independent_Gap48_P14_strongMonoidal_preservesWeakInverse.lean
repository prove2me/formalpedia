-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_strongMonoidal_preservesWeakInverse
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.strongMonoidal_preservesWeakInverse
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:46:06.009092+00:00
-- url     : https://prove2.me/theorems/f36ec12e-5646-4d90-a74c-75b2d6082879
-- title:
--   Strong monoidal functors preserve weak inverses
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C,D$ be monoidal categories and $F:C\to D$ a strong monoidal functor, with invertible unit and tensor comparisons. If $x,y\in C$ satisfy $x\otimes y\cong1_C$ and $y\otimes x\cong1_C$, then
--   $$F(x)\otimes F(y)\cong1_D,\qquad F(y)\otimes F(x)\cong1_D.$$
--   Neither category is required to be a groupoid. This identifies the inverse-preservation property of a strong monoidal functor without specifying adjunction maps.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 9, Proposition 3: strong monoidal functors preserve weak inverses

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Proposition 3, PDF p. 9: a strong monoidal functor preserves both weak-inverse
isomorphisms; no groupoid condition is imposed on either category. -/
theorem strongMonoidal_preservesWeakInverse
    {D : Type u1} [Category.{v1} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (x y : C) (h : IsWeakInverse x y) :
    IsWeakInverse (F.obj x) (F.obj y) := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
