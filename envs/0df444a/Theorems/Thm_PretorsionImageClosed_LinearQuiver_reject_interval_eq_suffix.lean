-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_reject_interval_eq_suffix
-- name    : PretorsionImageClosed.LinearQuiver.reject_interval_eq_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:37:45.257874+00:00
-- url     : https://prove2.me/theorems/3c2913d4-cf05-5e70-9208-3f1fb28223b6
-- title:
--   Linear Quiver: reject interval eq suffix
-- statement:
--   Lemma 6.3: the reject of `M_{c,d}` is the suffix `M_{b+1,d}` for the largest `b ∈ [c, d]`
--   with `M_{c,b} ∈ F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L159-L191
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L159-L191

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
variable {T F : Subcategory (Statement.LinRep k n)}

theorem PretorsionImageClosed.LinearQuiver.reject_interval_eq_suffix (hF : F.IsSubobjectClosed) {c ℓ d v : Fin n} (hℓd : ℓ ≤ d)
    (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) (hb : F.prop (interval k c ℓ))
    (hmax : ∀ j, ℓ < j → j ≤ d → ¬ F.prop (interval k c j)) :
    F.reject (interval k c d) = suffix c d v hcv := by sorry
