-- Prove2me | Theorems.Thm_SNumbers_exists_projection_range_eq_of_rank_le
-- name    : SNumbers.exists_projection_range_eq_of_rank_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:24:35.353231+00:00
-- url     : https://prove2.me/theorems/85807509-3116-42a6-acd5-f710082ba827
-- title:
--   SNumbers: exists projection range eq of rank le
-- statement:
--   **Kadets–Snobar theorem.** Every finite-dimensional subspace `V` of a normed
--   space `Y` of dimension at most `n` is the range of a bounded projection
--   `P : Y →L[𝕜] Y` (`P ∘ P = P`) with operator norm `‖P‖ ≤ √n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/KadetsSnobar.lean#L41-L50
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/KadetsSnobar.lean#L41-L50

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_BasicResults_John
public import Definitions.Def_BasicResults_KadetsSnobar
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.exists_projection_range_eq_of_rank_le
    {V : Submodule 𝕜 Y} {n : ℕ} (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt n := by sorry
