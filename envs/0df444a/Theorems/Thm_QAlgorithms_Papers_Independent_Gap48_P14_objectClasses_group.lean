-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_objectClasses_group
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.objectClasses_group
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:49:19.011995+00:00
-- url     : https://prove2.me/theorems/c0e985f2-dce7-4188-9787-5b3c729b6b24
-- title:
--   Object isomorphism classes form a group
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a weak 2-group. Let $\pi_0(C)$ be the quotient of its object type by the relation of being isomorphic, and write $[x]$ for the class of $x$. There is a group structure on this actual quotient satisfying
--   $$[x][y]=[x\otimes y],\qquad 1=[1_C],\qquad [x]^{-1}=[y]\ \text{whenever }y\text{ is a weak inverse of }x.$$
--   No skeletal presentation, strict tensor inverses, or trivial associator is assumed. This supplies the intrinsic group of components used in cohomological classification.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 5, Sections 1 and 8.3: group of object isomorphism classes

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

/-- Sections 1 and 8.3, PDF pp. 5,56,58: the actual quotient carries the group
law [x][y]=[x tensor y], unit [1], and inverse [y] for every weak inverse y of x. -/
theorem objectClasses_group {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (h : IsWeakTwoGroup C) :
    ∃ g : Group (ObjectClasses C),
      letI := g
      (∀ x y : C, objectClass x * objectClass y = objectClass (x ⊗ y)) ∧
      (1 : ObjectClasses C) = objectClass (𝟙_ C) ∧
      (∀ x y : C, IsWeakInverse x y → (objectClass x)⁻¹ = objectClass y) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P14
