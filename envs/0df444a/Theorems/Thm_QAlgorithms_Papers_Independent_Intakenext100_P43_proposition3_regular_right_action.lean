-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_proposition3_regular_right_action
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.proposition3_regular_right_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:48:59.022819+00:00
-- url     : https://prove2.me/theorems/6715dfad-578a-4a46-b377-f7980815ca9b
-- title:
--   Multiplication is the regular right action
-- statement:
--   Let $\mathcal C$ be a category with finite products and let $G$ be an internal group, with multiplication $m:G\times G\to G$, unit $e:1\to G$ and inverse. Then $r=m$ is a right action of $G$ on $G$: for all generalized elements $w,x,y:T\to G$,
--
--   $$r(r(w,x),y)=r(w,m(x,y)),\qquad r(w,e)=w.$$
--
--   In the category of smooth spaces these are smooth internal operations. The result fixes the regular action used in the definition of principal bundles.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 16, Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

variable [CartesianMonoidalCategory C]

/-- Proposition 3, PDF p. 16: the action is the specified multiplication
map, rather than an unspecified action on the group. -/
theorem proposition3_regular_right_action (G : C) [GrpObj G] :
    IsRightAction G G (MonObj.mul (X := G)) := by sorry

end Ordinary

end QAlgorithms.Papers.Independent.Intakenext100.P43
