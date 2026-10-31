-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGrpAndGroupCat
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.internalGrpAndGroupCat
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:31:39.829576+00:00
-- url     : https://prove2.me/theorems/fe086694-0838-402a-9ec3-652251559d37
-- title:
--   Internal Grp categories correspond to group objects in Cat
-- statement:
--   Let $O$ and $A$ be groups, equipped with source, target, identity and partial composition maps defining a small category. This is an internal category in Grp exactly when pointwise multiplication, unit and inversion on objects and arrows define a strict group object in Cat. The multiplication functor has
--
--   $$\mu_O(x,y)=xy,\qquad\mu_A(f,g)=fg.$$
--
--   The unit functor from the one-object discrete category picks out $1_O$ and $1_A$, and the inversion functor uses the two group inversions. In the reverse translation these functors give precisely the same group operations and category maps. Functoriality of multiplication is the interchange law; the original group structures supply associativity and both inverse laws. This states the source's inverse structure translations, without enlarging the assertion to an equivalence of unspecified categories of internal functors.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 8, §3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 8: the explicit mutually inverse structure translations between
internal Grp categories and strict group objects in Cat. Under total-arrow
coordinates both translations retain the category and BOTH pointwise groups.
This claims no additional equivalence of categories of internal functors. -/
theorem internalGrpAndGroupCat {A : Type u} {O : Type v} [Group A] [Group O]
    (D : CategoryMaps A O) :
    InternalCategoryInGrp D ↔ GroupObjectInCat D := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
