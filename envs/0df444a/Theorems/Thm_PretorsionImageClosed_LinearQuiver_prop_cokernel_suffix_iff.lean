-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_cokernel_suffix_iff
-- name    : PretorsionImageClosed.LinearQuiver.prop_cokernel_suffix_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:34:11.010826+00:00
-- url     : https://prove2.me/theorems/96362e5a-28f7-4c61-a42c-b8293bb0ff0d
-- title:
--   Linear Quiver: prop cokernel suffix iff
-- statement:
--   The Linear Quiver construction uses the prop cokernel suffix iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L117-L120
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L117-L120

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

theorem PretorsionImageClosed.LinearQuiver.prop_cokernel_suffix_iff (Z : Subcategory (Statement.LinRep k n)) {c ℓ d v : Fin n}
    (hℓd : ℓ ≤ d) (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) :
    Z.prop (cokernel (suffix (k := k) c d v hcv).arrow) ↔ Z.prop (interval k c ℓ) := by sorry
