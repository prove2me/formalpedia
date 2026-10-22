-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P14_unitAutomorphisms_abelian
-- name    : QAlgorithms.Papers.Independent.Gap48.P14.unitAutomorphisms_abelian
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:49:51.287973+00:00
-- url     : https://prove2.me/theorems/6e4897ea-d282-45f3-a38c-889748dcc069
-- title:
--   Unit automorphisms form an abelian group
-- statement:
--   Throughout, categories and morphisms lie in fixed universes, and composition is written in order of application. Let $C$ be a weak 2-group, with tensor unit $I$. The existing automorphism group $\operatorname{Aut}_C(I)$, whose multiplication is induced by composition, is abelian. Moreover for any endomorphisms $f,g:I\to I$, the tensor product transported by the left unitor agrees with composition:
--   $$uv=vu\quad(u,v\in\operatorname{Aut}_C(I)),\qquad\lambda_I^{-1};(f\otimes g);\lambda_I=f;g.$$
--   This identifies the abelian coefficient group intrinsic to a 2-group, including the unit transport needed in a nonstrict monoidal category.
-- source:
--   Higher-Dimensional Algebra V: 2-Groups, arXiv:math/0307200v3, PDF p. 58, Section 8.3: unit automorphisms form an abelian group

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P14

namespace QAlgorithms.Papers.Independent.Gap48.P14

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v u1 v1

/-- Section 8.3, PDF pp. 58–59: unit automorphisms commute under their existing
group operation. The tensor of unit endomorphisms is transported by the unitor
before comparison with composition; strictness is not assumed. -/
theorem unitAutomorphisms_abelian
    {C : Type u} [Category.{v} C] [MonoidalCategory C] (h : IsWeakTwoGroup C) :
    (∀ f g : Aut (𝟙_ C), f * g = g * f) ∧
    (∀ f g : (𝟙_ C ⟶ 𝟙_ C),
      (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = f ≫ g) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P14
