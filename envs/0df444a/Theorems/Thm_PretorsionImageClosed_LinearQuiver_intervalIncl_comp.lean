-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalIncl_comp
-- name    : PretorsionImageClosed.LinearQuiver.intervalIncl_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:09:49.636961+00:00
-- url     : https://prove2.me/theorems/6c1d2dbf-67b9-4f69-afb7-782dc723ed89
-- title:
--   Linear Quiver: interval Incl comp
-- statement:
--   The Linear Quiver construction uses the interval Incl comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L98-L105
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L98-L105

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

theorem PretorsionImageClosed.LinearQuiver.intervalIncl_comp {a ℓ ℓ' d : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    intervalIncl k d h' ≫ intervalIncl k d h = intervalIncl k d (h.trans h') := by sorry
