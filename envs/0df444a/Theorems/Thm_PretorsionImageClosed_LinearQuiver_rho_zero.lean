-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_rho_zero
-- name    : PretorsionImageClosed.LinearQuiver.rho_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:27:37.935406+00:00
-- url     : https://prove2.me/theorems/b4dd08eb-718b-467d-b6be-1eb5e5bec23b
-- title:
--   Linear Quiver: rho zero
-- statement:
--   For `n = 0` there are no vertices and `ρ = 0`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L173-L181
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Counting.lean#L173-L181

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

theorem PretorsionImageClosed.LinearQuiver.rho_zero (D : Subcategory (Statement.LinRep k 0)) : rho D.prop = 0 := by sorry
