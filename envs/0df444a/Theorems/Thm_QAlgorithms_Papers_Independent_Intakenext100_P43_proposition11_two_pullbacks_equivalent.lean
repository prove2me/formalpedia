-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_proposition11_two_pullbacks_equivalent
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.proposition11_two_pullbacks_equivalent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:50:43.830587+00:00
-- url     : https://prove2.me/theorems/81f13d6a-a351-4d40-a50c-1a226bb64ca5
-- title:
--   Weak 2-pullbacks of the same cospan are equivalent
-- statement:
--   Let $\mathcal C$ be a bicategory, $f:X\to Z$ and $g:Y\to Z$ two 1-morphisms, and $P,Q$ two specified weak 2-pullback cones for this cospan. The weak universal property is precisely that of §2.1.3: every cone admits a cone morphism to the chosen cone, and any other such lift is related to it by a unique invertible 2-cell compatible with both projection comparisons. Then there are 1-morphisms $a:P\to Q$ and $b:Q\to P$ and invertible 2-cells
--
--   $$a;b\cong\operatorname{id}_P,\qquad b;a\cong\operatorname{id}_Q.$$
--
--   Thus the vertices are equivalent in $\mathcal C$. All comparison cells and ambient associators are retained; no global existence of 2-pullbacks is assumed.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 30, Proposition 11

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section WeakPullbacks

open CategoryTheory.Bicategory

variable {D : Type u} [Bicategory.{w, v} D]

/-- Proposition 11, PDF pp. 30–31: two specified weak 2-pullbacks
are equivalent objects of the ambient bicategory. Both inverse directions
and invertible composite-to-identity cells are retained; no equality of
vertices or global existence of 2-pullbacks is asserted. -/
theorem proposition11_two_pullbacks_equivalent
    {X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z)
    (P Q : TwoPullbackCone f g)
    (hp : IsWeakTwoPullback P) (hq : IsWeakTwoPullback Q) :
    ∃ (a : P.vertex ⟶ Q.vertex) (b : Q.vertex ⟶ P.vertex),
      Nonempty (a ≫ b ≅ 𝟙 P.vertex) ∧ Nonempty (b ≫ a ≅ 𝟙 Q.vertex) := by sorry

end WeakPullbacks

end QAlgorithms.Papers.Independent.Intakenext100.P43
