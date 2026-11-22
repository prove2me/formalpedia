-- Prove2me | Theorems.Thm_P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69
-- name    : P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:59.106347+00:00
-- url     : https://prove2.me/theorems/e81c6649-3201-4a5a-aae7-7d53021aa152
-- title:
--   P2 M GJKKL Main Regime d  le E f590cd77fc69: P2 M GJKKL Main Regime d  le E f590cd77fc69
-- statement:
--   The P2 M GJKKL Main Regime d  le E f590cd77fc69 construction uses the P2 M GJKKL Main Regime d  le E f590cd77fc69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L146-L146
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L146-L146

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

theorem P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69 : d ^ (1 - ε) ≤ d ^ (1 - ε / 8) := by sorry

alias «GJKKL».«Main».«Regime».«dε_le_E» := P2M_GJKKL_Main_Regime_d__le_E_f590cd77fc69
