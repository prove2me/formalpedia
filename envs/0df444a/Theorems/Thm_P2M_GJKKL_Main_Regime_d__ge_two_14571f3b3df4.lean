-- Prove2me | Theorems.Thm_P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4
-- name    : P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:59.7248+00:00
-- url     : https://prove2.me/theorems/f42fa1ad-d5ef-4066-9f2b-98059c33be27
-- title:
--   P2 M GJKKL Main Regime d  ge two 14571f3b3df4: P2 M GJKKL Main Regime d  ge two 14571f3b3df4
-- statement:
--   The P2 M GJKKL Main Regime d  ge two 14571f3b3df4 construction uses the P2 M GJKKL Main Regime d  ge two 14571f3b3df4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L169-L169
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L169-L169

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

theorem P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4 : 2 ≤ d ^ ε := by sorry

alias «GJKKL».«Main».«Regime».«dε_ge_two» := P2M_GJKKL_Main_Regime_d__ge_two_14571f3b3df4
