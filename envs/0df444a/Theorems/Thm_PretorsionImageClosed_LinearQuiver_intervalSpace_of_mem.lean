-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSpace_of_mem
-- name    : PretorsionImageClosed.LinearQuiver.intervalSpace_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:49:26.324713+00:00
-- url     : https://prove2.me/theorems/3920651c-9e26-41e6-98e0-7589ca5c81cb
-- title:
--   Linear Quiver: interval Space of mem
-- statement:
--   The Linear Quiver construction uses the interval Space of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L79-L80
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L79-L80

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

theorem PretorsionImageClosed.LinearQuiver.intervalSpace_of_mem {a d i : Fin n} (h : a ≤ i ∧ i ≤ d) :
    intervalSpace k a d i = ⊤ := by sorry
