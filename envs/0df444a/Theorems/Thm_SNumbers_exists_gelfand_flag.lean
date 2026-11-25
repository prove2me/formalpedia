-- Prove2me | Theorems.Thm_SNumbers_exists_gelfand_flag
-- name    : SNumbers.exists_gelfand_flag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:09:16.445581+00:00
-- url     : https://prove2.me/theorems/da3ebdb5-605d-5af0-a4ae-314d20d19426
-- title:
--   SNumbers: exists gelfand flag
-- statement:
--   **Gelfand flag.** From `0 < γ < cₙ(S)`: vectors `x j` of the unit ball and
--   norming functionals `ρ j` with `ρ j (S (x j)) = γ` and `ρ i (S (x j)) = 0` for
--   `i < j`. Rescaling the unit-image vectors of `exists_next_vector` by `γ` puts
--   them into the unit ball.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L462-L511
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L462-L511

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.exists_gelfand_flag (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (ρ : Fin m → (Y →L[𝕜] 𝕜)),
      (∀ j, ‖x j‖ ≤ 1) ∧ (∀ j, ‖ρ j‖ ≤ 1) ∧
      (∀ j, ρ j (S (x j)) = ((γ : ℝ) : 𝕜)) ∧
      (∀ i j : Fin m, i < j → ρ i (S (x j)) = 0) := by sorry
