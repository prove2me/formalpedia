-- Prove2me | Theorems.Thm_P2M_Malliavin_symmetrize__comp_symmetrize__14ce21f0a046
-- name    : P2M_Malliavin_symmetrize__comp_symmetrize__14ce21f0a046
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:55:16.437252+00:00
-- url     : https://prove2.me/theorems/3a1cca00-0a25-5603-85f9-64cb9b446936
-- title:
--   P2 M Malliavin symmetrize  comp symmetrize  14ce21f0a046: P2 M Malliavin symmetrize  comp symmetrize  14ce21f0a046
-- statement:
--   The P2 M Malliavin symmetrize  comp symmetrize  14ce21f0a046 construction uses the P2 M Malliavin symmetrize  comp symmetrize  14ce21f0a046 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L154-L157
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L154-L157

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

theorem P2M_Malliavin_symmetrize__comp_symmetrize__14ce21f0a046 (n : ℕ) :
    (symmetrizeₗ n : ((Fin n → T) → E) →ₗ[ℝ] ((Fin n → T) → E)).comp (symmetrizeₗ n) =
      symmetrizeₗ n := by sorry

alias «Malliavin».«symmetrizeₗ_comp_symmetrizeₗ» := P2M_Malliavin_symmetrize__comp_symmetrize__14ce21f0a046
