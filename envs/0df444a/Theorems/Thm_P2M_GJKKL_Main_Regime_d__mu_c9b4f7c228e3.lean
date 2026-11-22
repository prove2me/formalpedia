-- Prove2me | Theorems.Thm_P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
-- name    : P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:30.018257+00:00
-- url     : https://prove2.me/theorems/cd3de022-db4b-4dbc-9ddb-b184e85cd650
-- title:
--   P2 M GJKKL Main Regime d  mu c9b4f7c228e3: P2 M GJKKL Main Regime d  mu c9b4f7c228e3
-- statement:
--   The P2 M GJKKL Main Regime d  mu c9b4f7c228e3 construction uses the P2 M GJKKL Main Regime d  mu c9b4f7c228e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L195-L196
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L195-L196

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

theorem P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3 : d ^ ε * d ^ (-(ε ^ 3)) = d ^ (ε - ε ^ 3) := by sorry

alias «GJKKL».«Main».«Regime».«dε_mu» := P2M_GJKKL_Main_Regime_d__mu_c9b4f7c228e3
