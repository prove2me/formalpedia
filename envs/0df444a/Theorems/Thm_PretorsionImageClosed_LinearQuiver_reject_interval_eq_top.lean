-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_reject_interval_eq_top
-- name    : PretorsionImageClosed.LinearQuiver.reject_interval_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:38:44.743905+00:00
-- url     : https://prove2.me/theorems/56e4dec3-fbe2-4adb-859a-42c55e987c6b
-- title:
--   Linear Quiver: reject interval eq top
-- statement:
--   Lemma 6.3: the reject of `M_{c,d}` is all of `M_{c,d}` when no nonzero quotient `M_{c,j}`
--   lies in `F`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L195-L211
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L195-L211

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

theorem PretorsionImageClosed.LinearQuiver.reject_interval_eq_top (hF : F.IsSubobjectClosed) {c d : Fin n} (hcd : c ≤ d)
    (h : ∀ j, c ≤ j → j ≤ d → ¬ F.prop (interval k c j)) : F.reject (interval k c d) = ⊤ := by sorry
