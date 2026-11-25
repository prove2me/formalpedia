-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_eq_bot_of_lt
-- name    : PretorsionImageClosed.LinearQuiver.suffix_eq_bot_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:08:02.564299+00:00
-- url     : https://prove2.me/theorems/45b4bc00-2ed7-5542-95c4-e1f6cb72749d
-- title:
--   Linear Quiver: suffix eq bot of lt
-- statement:
--   The Linear Quiver construction uses the suffix eq bot of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L114-L116
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L114-L116

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

theorem PretorsionImageClosed.LinearQuiver.suffix_eq_bot_of_lt {a d ℓ : Fin n} (h : a ≤ ℓ) (hℓ : d < ℓ) : suffix (k := k) a d ℓ h = ⊥ := by sorry
