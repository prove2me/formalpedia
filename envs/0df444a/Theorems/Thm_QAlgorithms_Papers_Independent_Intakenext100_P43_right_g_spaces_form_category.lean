-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_right_g_spaces_form_category
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.right_g_spaces_form_category
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:50:08.113998+00:00
-- url     : https://prove2.me/theorems/897b5e34-af43-40af-9864-af2ecf02ad95
-- title:
--   Right G-spaces and equivariant maps form a category
-- statement:
--   Let $\mathcal C$ be a category with finite products and let $G$ be an internal group. Objects are all internal right $G$-spaces $(F,r)$; morphisms are all maps $t:F\to F'$ satisfying $t(r(w,x))=r'(t(w),x)$ for every pair of generalized elements. With the prescribed operations
--
--   $$\operatorname{id}_{(F,r)}=\operatorname{id}_F,\qquad (t,t')\longmapsto t'\circ t,$$
--
--   these objects and morphisms form a category. No action is required to be faithful, free or transitive. This is the category used to compare fibres as $G$-spaces.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 16, g-spaces-category

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

variable [CartesianMonoidalCategory C]

/-- The unnumbered category claim in §1.4.4, PDF p. 16. The morphisms
are exactly all equivariant maps, with the operations already prescribed. -/
theorem right_g_spaces_form_category (G : C) [GrpObj G] :
    ∃ cat : Category (RightGSpace G),
      cat.toCategoryStruct = rightGSpaceCategoryStruct G := by sorry

end Ordinary

end QAlgorithms.Papers.Independent.Intakenext100.P43
