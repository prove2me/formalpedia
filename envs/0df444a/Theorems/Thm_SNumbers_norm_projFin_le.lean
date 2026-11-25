-- Prove2me | Theorems.Thm_SNumbers_norm_projFin_le
-- name    : SNumbers.norm_projFin_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:24:46.541812+00:00
-- url     : https://prove2.me/theorems/cec53634-f26e-43f5-8e10-84047c456ce6
-- title:
--   SNumbers: norm proj Fin le
-- statement:
--   The coordinate projection is a contraction: `‖projFin h x‖ ≤ ‖x‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L106-L125
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L106-L125

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SNumbers.norm_projFin_le (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) :
    ‖projFin (p := p) h x‖ ≤ ‖x‖ := by sorry
