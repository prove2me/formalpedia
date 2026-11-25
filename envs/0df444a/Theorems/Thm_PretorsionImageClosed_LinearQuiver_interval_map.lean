-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_interval_map
-- name    : PretorsionImageClosed.LinearQuiver.interval_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:59:08.222852+00:00
-- url     : https://prove2.me/theorems/1fe721be-0a4e-40cd-945e-96e38a810c1d
-- title:
--   Linear Quiver: interval map
-- statement:
--   The Linear Quiver construction uses the interval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L145-L147
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/Interval.lean#L145-L147

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

theorem PretorsionImageClosed.LinearQuiver.interval_map (a d : Fin n) {i j : Fin n} (f : i ⟶ j) :
    (interval k a d).map f =
      FGModuleCat.ofHom (inclusionOrZero k (intervalSpace k a d i) (intervalSpace k a d j)) := by sorry
