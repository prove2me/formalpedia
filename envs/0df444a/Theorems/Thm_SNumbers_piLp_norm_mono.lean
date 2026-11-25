-- Prove2me | Theorems.Thm_SNumbers_piLp_norm_mono
-- name    : SNumbers.piLp_norm_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:45:07.546642+00:00
-- url     : https://prove2.me/theorems/5fb866fa-4de3-4c19-ac05-355ead5ae882
-- title:
--   SNumbers: pi Lp norm mono
-- statement:
--   If `‖x i‖ ≤ ‖y i‖` for every coordinate `i`, then `‖x‖ ≤ ‖y‖` in `PiLp p`.
--   Proved by the `p = ∞` (suprema) and `1 ≤ p.toReal` (sums of `p`-th powers)
--   cases of the explicit norm formula.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L50-L61
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L50-L61

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

theorem SNumbers.piLp_norm_mono {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] {x y : PiLp p β}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by sorry
