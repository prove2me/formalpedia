-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_isZero_interval_obj_of_not_mem
-- name    : PretorsionImageClosed.LinearQuiver.isZero_interval_obj_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:30.799123+00:00
-- url     : https://prove2.me/theorems/c5785e8f-47e9-4053-9bb7-8c5de70df3d0
-- title:
--   Linear Quiver: is Zero interval obj of not mem
-- statement:
--   The Linear Quiver construction uses the is Zero interval obj of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L155-L160
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L155-L160

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

theorem PretorsionImageClosed.LinearQuiver.isZero_interval_obj_of_not_mem {a d i : Fin n} (h : ¬ (a ≤ i ∧ i ≤ d)) :
    IsZero ((interval k a d).obj i) := by sorry
