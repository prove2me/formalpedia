-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_improvement_diagrams_equal
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.improvement_diagrams_equal
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:47:38.902639+00:00
-- url     : https://prove2.me/theorems/c98e5477-2f9a-4996-8d31-fcb00d6fdd4a
-- title:
--   Equality of the two improvement diagrams
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a monoidal category with objects $x,y$ and specified isomorphisms $i:1\cong x\otimes y$, $e:y\otimes x\cong1$, without assuming a zig-zag identity. Put $z=x\otimes y$ and define
--   $$P=i;(1_x\otimes\lambda_y^{-1});(1_x\otimes(e^{-1}\otimes1_y));(1_x\otimes a_{y,x,y});a_{x,y,z}^{-1}.$$
--   The two composites from the unit to $x\otimes y$ are
--   $$J_L=P;(i^{-1}\otimes1_z);a_{1,x,y}^{-1};(\lambda_x\otimes1_y),\qquad J_R=P;(1_z\otimes i^{-1});\rho_z.$$
--   Here $a$, $\lambda$ and $\rho$ are the associator and the left and right unitors, and semicolons denote composition in order of application.
--   Then the two displayed string diagrams of Lemma 15 represent equal morphisms:
--   $$J_L(i,e)=J_R(i,e).$$
--   Thus cancelling either the first or the last $x\otimes y$ pair in the improvement construction gives the same unit.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 20, Lemma 15: equality of two improvement string diagrams

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Lemma 15, PDF pp. 20–21: equality of the two displayed improvement diagrams.
No zig-zag identity for the initial inverse data is assumed. -/
theorem improvement_diagrams_equal (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) :
    (improvedUnitIso i e).hom = (alternativeUnitIso i e).hom := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
