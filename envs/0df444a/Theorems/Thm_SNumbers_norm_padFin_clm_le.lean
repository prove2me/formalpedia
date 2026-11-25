-- Prove2me | Theorems.Thm_SNumbers_norm_padFin_clm_le
-- name    : SNumbers.norm_padFin_clm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:45:19.318307+00:00
-- url     : https://prove2.me/theorems/768871a9-3f1a-488e-aa35-df09021400a6
-- title:
--   SNumbers: norm pad Fin clm le
-- statement:
--   The coordinate embedding has operator norm `≤ 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L170-L173
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L170-L173

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

theorem SNumbers.norm_padFin_clm_le (h : n ≤ m) :
    ‖(padFin (𝕜 := 𝕜) (p := p) (n := n) (m := m))‖ ≤ 1 := by sorry
