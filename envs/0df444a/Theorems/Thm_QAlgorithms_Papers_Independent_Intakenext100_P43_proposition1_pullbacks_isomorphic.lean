-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_proposition1_pullbacks_isomorphic
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.proposition1_pullbacks_isomorphic
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:47:57.813695+00:00
-- url     : https://prove2.me/theorems/a4c55025-b752-4951-bac1-d1ab3b3ebe3e
-- title:
--   Pullbacks of one cospan have isomorphic vertices
-- statement:
--   Let $\mathcal C$ be a category and let $f:X\to Z$ and $g:Y\to Z$ be morphisms. Suppose that $(P,p_1,p_2)$ and $(Q,q_1,q_2)$ are limiting cones over this same cospan. Then
--
--   $$P\cong Q.$$
--
--   Only these two limiting cones are assumed to exist. This makes constructions using a chosen pullback independent of that choice up to isomorphism.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 6, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

/-- Proposition 1, PDF p. 6: two limiting cones over the same cospan
have isomorphic vertices. No global existence of pullbacks is required. -/
theorem proposition1_pullbacks_isomorphic
    {X Y Z P Q : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p1 : P ⟶ X) (p2 : P ⟶ Y) (q1 : Q ⟶ X) (q2 : Q ⟶ Y)
    (hp : IsPullback p1 p2 f g) (hq : IsPullback q1 q2 f g) :
    Nonempty (P ≅ Q) := by sorry

end Ordinary

end QAlgorithms.Papers.Independent.Intakenext100.P43
