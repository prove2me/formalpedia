-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_cokernel_top_arrow
-- name    : PretorsionImageClosed.LinearQuiver.prop_cokernel_top_arrow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:42:20.606841+00:00
-- url     : https://prove2.me/theorems/5b5d4345-3b30-4066-9fc7-4d0995041658
-- title:
--   Linear Quiver: prop cokernel top arrow
-- statement:
--   The Linear Quiver construction uses the prop cokernel top arrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L122-L124
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L122-L124

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.prop_cokernel_top_arrow (Z : Subcategory (Statement.LinRep k n)) (X : Statement.LinRep k n) :
    Z.prop (cokernel (⊤ : Subobject X).arrow) := by sorry
