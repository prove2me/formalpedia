-- Prove2me | Theorems.Thm_P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46
-- name    : P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:23.767483+00:00
-- url     : https://prove2.me/theorems/143c1118-e572-4082-88fc-1e7fab580bdf
-- title:
--   P2 M GJKKL Main Regime   le one 1ecfd2c91c46: P2 M GJKKL Main Regime   le one 1ecfd2c91c46
-- statement:
--   The P2 M GJKKL Main Regime   le one 1ecfd2c91c46 construction uses the P2 M GJKKL Main Regime   le one 1ecfd2c91c46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L80-L84
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L80-L84

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Definitions.Def_GJKKL_Main_Parameters
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R

theorem P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46 : ε ≤ 1 := by sorry

alias «GJKKL».«Main».«Regime».«ε_le_one» := P2M_GJKKL_Main_Regime___le_one_1ecfd2c91c46
