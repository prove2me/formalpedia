-- Prove2me | Theorems.Thm_PretorsionImageClosed_sumSubobject_eq_right_of_le
-- name    : PretorsionImageClosed.sumSubobject_eq_right_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:12:14.040652+00:00
-- url     : https://prove2.me/theorems/849fd4c8-0c81-56fd-a4e6-018fb33a1f36
-- title:
--   Pretorsion Image Closed: sum Subobject eq right of le
-- statement:
--   The Pretorsion Image Closed construction uses the sum Subobject eq right of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L32-L39
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/SummandReduction.lean#L32-L39

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]

theorem PretorsionImageClosed.sumSubobject_eq_right_of_le {X : C} {S S' : Subobject X} (h : S ≤ S') :
    sumSubobject S S' = S' := by sorry
