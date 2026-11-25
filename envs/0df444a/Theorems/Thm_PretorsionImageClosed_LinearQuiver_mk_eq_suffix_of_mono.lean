-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_mk_eq_suffix_of_mono
-- name    : PretorsionImageClosed.LinearQuiver.mk_eq_suffix_of_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:12:59.348799+00:00
-- url     : https://prove2.me/theorems/5c5dd74d-b477-41c7-809a-9b5e6f41000f
-- title:
--   Linear Quiver: mk eq suffix of mono
-- statement:
--   A monomorphism `M_{c,d} ⟶ M_{a,d}` (with `a ≤ c ≤ d`) defines the suffix
--   subobject `M_{c,d}`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L237-L253
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L237-L253

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

theorem PretorsionImageClosed.LinearQuiver.mk_eq_suffix_of_mono {a c d : Fin n} (hac : a ≤ c) (hcd : c ≤ d)
    (η : interval k c d ⟶ interval k a d) [Mono η] : Subobject.mk η = suffix a d c hac := by sorry
