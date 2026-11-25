-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
-- name    : PretorsionImageClosed.LinearQuiver.eq_bot_or_eq_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:07:20.912883+00:00
-- url     : https://prove2.me/theorems/050fff7f-2535-5b83-9a8b-bce23971265f
-- title:
--   Linear Quiver: eq bot or eq suffix
-- statement:
--   Every subobject of `M_{a,d}` is zero or a suffix `M_{ℓ,d}` with `a ≤ ℓ ≤ d` (5.1).
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L256-L295
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L256-L295

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

theorem PretorsionImageClosed.LinearQuiver.eq_bot_or_eq_suffix {a d : Fin n} (K : Subobject (interval k a d)) :
    K = ⊥ ∨ ∃ (ℓ : Fin n) (hal : a ≤ ℓ), ℓ ≤ d ∧ K = suffix a d ℓ hal := by sorry
