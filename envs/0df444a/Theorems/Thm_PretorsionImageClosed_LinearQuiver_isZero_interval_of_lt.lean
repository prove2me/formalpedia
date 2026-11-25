-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_isZero_interval_of_lt
-- name    : PretorsionImageClosed.LinearQuiver.isZero_interval_of_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:09:15.368807+00:00
-- url     : https://prove2.me/theorems/85e2237f-bba5-4397-b598-b885376f7c0e
-- title:
--   Linear Quiver: is Zero interval of lt
-- statement:
--   The Linear Quiver construction uses the is Zero interval of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L107-L108
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L107-L108

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

theorem PretorsionImageClosed.LinearQuiver.isZero_interval_of_lt {ℓ d : Fin n} (h : d < ℓ) : IsZero (interval k ℓ d) := by sorry
