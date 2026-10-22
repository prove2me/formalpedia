-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_triangle_equivalence
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.triangle_equivalence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:46:38.443123+00:00
-- url     : https://prove2.me/theorems/9f3fd56b-728b-44bd-afa5-53c77e0f1de0
-- title:
--   Either inverse zig-zag implies the other
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a monoidal category, let $x,y\in C$, and specify isomorphisms $i:1\cong x\otimes y$ and $e:y\otimes x\cong1$. Then
--   $$((i\otimes1_x);a_{x,y,x};(1_x\otimes e)=\lambda_x;\rho_x^{-1})\quad\Longleftrightarrow\quad((1_y\otimes i);a_{y,x,y}^{-1};(e\otimes1_y)=\rho_y;\lambda_y^{-1}).$$
--   The maps $a,\lambda,\rho$ are the monoidal associator and unitors. This permits either triangle law to be used to specify an adjoint equivalence once the unit and counit are invertible.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 17, Proposition 13: either zig-zag identity implies the other

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

section Inverses

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Proposition 13, PDF pp. 17–19: either zig-zag implies the other.
The supplied unit and counit are isomorphisms, without a triangle assumption. -/
theorem triangle_equivalence (x y : C) (i : 𝟙_ C ≅ x ⊗ y)
    (e : y ⊗ x ≅ 𝟙_ C) :
    FirstTriangle i e ↔ SecondTriangle i e := by sorry

end Inverses

end QAlgorithms.Papers.Independent.Gap48.P14
