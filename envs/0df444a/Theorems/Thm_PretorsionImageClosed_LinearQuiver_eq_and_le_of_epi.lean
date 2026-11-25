-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_epi
-- name    : PretorsionImageClosed.LinearQuiver.eq_and_le_of_epi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:30:30.003871+00:00
-- url     : https://prove2.me/theorems/f8563743-a88a-43ba-848c-b0c1cead53be
-- title:
--   Linear Quiver: eq and le of epi
-- statement:
--   An epimorphism `M_{a,d} ⟶ M_{a',d'}` between nonzero intervals has `a' = a` and
--   `d' ≤ d`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L197-L211
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L197-L211

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

theorem PretorsionImageClosed.LinearQuiver.eq_and_le_of_epi {a d a' d' : Fin n} (had' : a' ≤ d') (η : interval k a d ⟶ interval k a' d')
    [Epi η] : a' = a ∧ d' ≤ d := by sorry
