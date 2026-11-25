-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_mono_biprod_desc
-- name    : PretorsionImageClosed.LinearQuiver.not_mono_biprod_desc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:54.202462+00:00
-- url     : https://prove2.me/theorems/5c15e0a2-cbc0-5898-86f5-87d6cacbd59c
-- title:
--   Linear Quiver: not mono biprod desc
-- statement:
--   There is no monomorphism from a direct sum of two intervals ending at `d`
--   into `M_{a,d}`: the kernel at the vertex `d` is nonzero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L152-L227
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L152-L227

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

theorem PretorsionImageClosed.LinearQuiver.not_mono_biprod_desc {a c c' d : Fin n} (hac : a ≤ c) (hac' : a ≤ c') (hcd : c ≤ d)
    (hcd' : c' ≤ d) (f : interval k c d ⟶ interval k a d) (g : interval k c' d ⟶ interval k a d) :
    ¬ Mono (biprod.desc f g) := by sorry
