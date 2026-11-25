-- Prove2me | Theorems.Thm_SNumbers_exists_projection_ker_eq_of_codim_le
-- name    : SNumbers.exists_projection_ker_eq_of_codim_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:24:38.153396+00:00
-- url     : https://prove2.me/theorems/da421969-cc93-471d-aa5a-5b0de3d78597
-- title:
--   SNumbers: exists projection ker eq of codim le
-- statement:
--   **Garling–Gordon theorem (ε-form).** For a closed subspace `M` of a normed
--   space `X` of codimension at most `n` and every `ε > 0`, there is a bounded
--   projection `P : X →L[𝕜] X` (`P ∘ P = P`) with kernel exactly `M` and operator
--   norm `‖P‖ ≤ √n + ε`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/GarlingGordon.lean#L46-L58
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/GarlingGordon.lean#L46-L58

module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_BasicResults_John
public import Definitions.Def_BasicResults_GarlingGordon
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem SNumbers.exists_projection_ker_eq_of_codim_le
    {M : Submodule 𝕜 X} (hM_closed : IsClosed (M : Set X)) {n : ℕ}
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧
      LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧ ‖P‖ ≤ Real.sqrt n + ε := by sorry
