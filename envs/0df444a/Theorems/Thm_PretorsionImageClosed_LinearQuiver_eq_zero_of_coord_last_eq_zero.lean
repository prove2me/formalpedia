-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_zero_of_coord_last_eq_zero
-- name    : PretorsionImageClosed.LinearQuiver.eq_zero_of_coord_last_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:11:22.583256+00:00
-- url     : https://prove2.me/theorems/2eb2f724-8f6c-495e-a83d-00f57e4a1833
-- title:
--   Linear Quiver: eq zero of coord last eq zero
-- statement:
--   A morphism `M_{c,d} ⟶ M_{a,d}` (with `a ≤ c ≤ d`) vanishing at the vertex `d`
--   is zero.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L142-L148
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Subobjects.lean#L142-L148

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

theorem PretorsionImageClosed.LinearQuiver.eq_zero_of_coord_last_eq_zero {a c d : Fin n} (hac : a ≤ c) (hcd : c ≤ d)
    (f : interval k c d ⟶ interval k a d) (h : coord f d = 0) : f = 0 := by sorry
