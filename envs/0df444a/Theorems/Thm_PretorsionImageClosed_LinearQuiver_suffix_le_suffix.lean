-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix
-- name    : PretorsionImageClosed.LinearQuiver.suffix_le_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:07:27.730328+00:00
-- url     : https://prove2.me/theorems/6310c2c7-d35e-5faf-8bf8-646f3de37d36
-- title:
--   Linear Quiver: suffix le suffix
-- statement:
--   The Linear Quiver construction uses the suffix le suffix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L125-L127
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L125-L127

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

theorem PretorsionImageClosed.LinearQuiver.suffix_le_suffix {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    suffix (k := k) a d ℓ' (h.trans h') ≤ suffix a d ℓ h := by sorry
