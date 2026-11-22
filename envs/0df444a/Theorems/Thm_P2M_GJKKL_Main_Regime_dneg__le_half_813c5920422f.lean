-- Prove2me | Theorems.Thm_P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f
-- name    : P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:26.011271+00:00
-- url     : https://prove2.me/theorems/bad71b78-83b2-4038-b21a-5aae8d1dadd3
-- title:
--   P2 M GJKKL Main Regime dneg  le half 813c5920422f: P2 M GJKKL Main Regime dneg  le half 813c5920422f
-- statement:
--   The P2 M GJKKL Main Regime dneg  le half 813c5920422f construction uses the P2 M GJKKL Main Regime dneg  le half 813c5920422f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L171-L173
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean#L171-L173

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

theorem P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f : d ^ (-ε) ≤ 1 / 2 := by sorry

alias «GJKKL».«Main».«Regime».«dnegε_le_half» := P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f
