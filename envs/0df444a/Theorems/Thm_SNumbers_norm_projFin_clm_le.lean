-- Prove2me | Theorems.Thm_SNumbers_norm_projFin_clm_le
-- name    : SNumbers.norm_projFin_clm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:45:11.630854+00:00
-- url     : https://prove2.me/theorems/66726321-2202-4f17-925e-d65e68fdb1a9
-- title:
--   SNumbers: norm proj Fin clm le
-- statement:
--   The coordinate projection has operator norm `≤ 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L128-L130
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L128-L130

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

theorem SNumbers.norm_projFin_clm_le (h : n ≤ m) : ‖projFin (𝕜 := 𝕜) (p := p) h‖ ≤ 1 := by sorry
