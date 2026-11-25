-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_imageSubobject_intervalIncl_comp_intervalProj
-- name    : PretorsionImageClosed.LinearQuiver.imageSubobject_intervalIncl_comp_intervalProj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:35:17.326284+00:00
-- url     : https://prove2.me/theorems/0eea7e05-c458-45db-8b74-6209250455b4
-- title:
--   Linear Quiver: image Subobject interval Incl comp interval Proj
-- statement:
--   The image of `M_{u,d} → M_{c,ℓ}` is the suffix `M_{u,ℓ}` of `M_{c,ℓ}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L76-L79
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L76-L79

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

theorem PretorsionImageClosed.LinearQuiver.imageSubobject_intervalIncl_comp_intervalProj {c u ℓ d : Fin n} (hcu : c ≤ u) (hℓd : ℓ ≤ d) :
    imageSubobject (intervalIncl k d hcu ≫ intervalProj k c hℓd) = suffix c ℓ u hcu := by sorry
