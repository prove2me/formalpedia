-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_self
-- name    : PretorsionImageClosed.LinearQuiver.suffix_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:07:38.458147+00:00
-- url     : https://prove2.me/theorems/537cd245-bab3-5444-ab76-07a6b74c7edf
-- title:
--   Linear Quiver: suffix self
-- statement:
--   The Linear Quiver construction uses the suffix self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L118-L123
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L118-L123

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

theorem PretorsionImageClosed.LinearQuiver.suffix_self (a d : Fin n) : suffix (k := k) a d a le_rfl = ⊤ := by sorry
