-- Prove2me | Theorems.Thm_P2M_Malliavin_symmetrize__isProj_bdeedc28d58a
-- name    : P2M_Malliavin_symmetrize__isProj_bdeedc28d58a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:18.479802+00:00
-- url     : https://prove2.me/theorems/9ee7b652-307e-5676-8532-91b7c2b459c1
-- title:
--   P2 M Malliavin symmetrize  is Proj bdeedc28d58a: P2 M Malliavin symmetrize  is Proj bdeedc28d58a
-- statement:
--   `symmetrizeₗ` is a linear projection onto the symmetric functions.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L173-L176
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L173-L176

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]

theorem P2M_Malliavin_symmetrize__isProj_bdeedc28d58a (n : ℕ) :
    LinearMap.IsProj (symmetricSubmodule T E n) (symmetrizeₗ n) := by sorry

alias «Malliavin».«symmetrizeₗ_isProj» := P2M_Malliavin_symmetrize__isProj_bdeedc28d58a
