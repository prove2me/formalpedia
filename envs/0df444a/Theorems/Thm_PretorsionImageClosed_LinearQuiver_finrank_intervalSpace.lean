-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_finrank_intervalSpace
-- name    : PretorsionImageClosed.LinearQuiver.finrank_intervalSpace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:01:47.495048+00:00
-- url     : https://prove2.me/theorems/9f6e2366-a98a-59b3-ad3f-85b35e9ae127
-- title:
--   Linear Quiver: finrank interval Space
-- statement:
--   The Linear Quiver construction uses the finrank interval Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L149-L153
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L149-L153

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Definitions.Def_PretorsionImageClosed_Modules_FiniteModules
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k]
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.finrank_intervalSpace (a d i : Fin n) :
    Module.finrank k (intervalSpace k a d i) = if a ≤ i ∧ i ≤ d then 1 else 0 := by sorry
