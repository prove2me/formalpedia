-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_end_eq
-- name    : PretorsionImageClosed.LinearQuiver.coord_end_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:29:24.031987+00:00
-- url     : https://prove2.me/theorems/fb1202d7-6c7d-4b5e-ba06-c89c4c27ad32
-- title:
--   Linear Quiver: coord end eq
-- statement:
--   An endomorphism of an interval is determined by one coordinate on the
--   interval.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L65-L72
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Indecomposables.lean#L65-L72

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

theorem PretorsionImageClosed.LinearQuiver.coord_end_eq {a d : Fin n} (had : a ≤ d) (p : interval k a d ⟶ interval k a d) (i : Fin n) :
    coord p i = coord p a * coord (𝟙 (interval k a d)) i := by sorry
