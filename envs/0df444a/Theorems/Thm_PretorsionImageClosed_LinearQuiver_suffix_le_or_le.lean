-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_or_le
-- name    : PretorsionImageClosed.LinearQuiver.suffix_le_or_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:09:59.285376+00:00
-- url     : https://prove2.me/theorems/1112bd8a-0a4d-4e4c-a221-444735c9d1e3
-- title:
--   Linear Quiver: suffix le or le
-- statement:
--   Subobjects of an interval are totally ordered: any two suffixes are comparable.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L130-L135
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L130-L135

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.suffix_le_or_le {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : a ≤ ℓ') :
    suffix (k := k) a d ℓ h ≤ suffix (k := k) a d ℓ' h' ∨
      suffix (k := k) a d ℓ' h' ≤ suffix (k := k) a d ℓ h := by sorry
