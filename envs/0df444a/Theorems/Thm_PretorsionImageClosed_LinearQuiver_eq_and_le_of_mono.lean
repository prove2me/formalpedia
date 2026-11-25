-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_mono
-- name    : PretorsionImageClosed.LinearQuiver.eq_and_le_of_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:29:39.701116+00:00
-- url     : https://prove2.me/theorems/2185b5c9-aeeb-4907-961f-0c487957f8d9
-- title:
--   Linear Quiver: eq and le of mono
-- statement:
--   A monomorphism `M_{a',d'} ⟶ M_{a,d}` between nonzero intervals has `d' = d` and
--   `a ≤ a'`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L175-L193
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L175-L193

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.eq_and_le_of_mono {a' d' a d : Fin n} (had' : a' ≤ d') (η : interval k a' d' ⟶ interval k a d)
    [Mono η] : d' = d ∧ a ≤ a' := by sorry
