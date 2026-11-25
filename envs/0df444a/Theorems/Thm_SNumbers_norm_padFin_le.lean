-- Prove2me | Theorems.Thm_SNumbers_norm_padFin_le
-- name    : SNumbers.norm_padFin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:46.411797+00:00
-- url     : https://prove2.me/theorems/ac10ea52-bc3a-4d0b-8eb1-6ca80ae4a70c
-- title:
--   SNumbers: norm pad Fin le
-- statement:
--   The coordinate embedding is an isometry, in particular a contraction:
--   `‖padFin y‖ ≤ ‖y‖`. The extra coordinates are zero, so they contribute nothing
--   to the `L^p` norm.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L141-L167
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L141-L167

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

theorem SNumbers.norm_padFin_le (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) :
    ‖padFin (p := p) (m := m) y‖ ≤ ‖y‖ := by sorry
