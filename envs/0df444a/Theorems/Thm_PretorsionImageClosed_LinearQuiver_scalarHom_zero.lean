-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_scalarHom_zero
-- name    : PretorsionImageClosed.LinearQuiver.scalarHom_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:08:07.716568+00:00
-- url     : https://prove2.me/theorems/4ba0f9c2-fad8-5fb6-a5bd-98490c0c2246
-- title:
--   Linear Quiver: scalar Hom zero
-- statement:
--   The Linear Quiver construction uses the scalar Hom zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L137-L138
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L137-L138

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

theorem PretorsionImageClosed.LinearQuiver.scalarHom_zero (a d : Fin n) : scalarHom a d (0 : k) = 0 := by sorry
