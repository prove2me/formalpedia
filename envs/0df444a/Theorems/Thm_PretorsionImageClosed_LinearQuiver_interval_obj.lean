-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_interval_obj
-- name    : PretorsionImageClosed.LinearQuiver.interval_obj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:01:34.018183+00:00
-- url     : https://prove2.me/theorems/cb27c3fb-d3ad-4dea-8fcc-32a815bc3a26
-- title:
--   Linear Quiver: interval obj
-- statement:
--   The Linear Quiver construction uses the interval obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L142-L143
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L142-L143

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

theorem PretorsionImageClosed.LinearQuiver.interval_obj (a d i : Fin n) :
    (interval k a d).obj i = FGModuleCat.of k (intervalSpace k a d i) := by sorry
