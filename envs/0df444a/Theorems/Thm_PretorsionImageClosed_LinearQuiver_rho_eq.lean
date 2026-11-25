-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_eq
-- name    : PretorsionImageClosed.LinearQuiver.rho_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:27:46.492062+00:00
-- url     : https://prove2.me/theorems/31d007f8-9661-4933-a497-718611b95b33
-- title:
--   Linear Quiver: rho eq
-- statement:
--   `ρ(D)` is the number of intervals of `D` ending at the last vertex.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L167-L168
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L167-L168

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalSets
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Counting
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
variable (C : Subcategory (Statement.LinRep k n))
variable {m : ℕ} (D : Subcategory (Statement.LinRep k (m + 1)))

theorem PretorsionImageClosed.LinearQuiver.rho_eq : rho D.prop = Nat.card (LastPairs D) := by sorry
