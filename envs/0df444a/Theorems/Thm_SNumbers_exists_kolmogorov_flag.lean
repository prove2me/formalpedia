-- Prove2me | Theorems.Thm_SNumbers_exists_kolmogorov_flag
-- name    : SNumbers.exists_kolmogorov_flag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:05:53.606037+00:00
-- url     : https://prove2.me/theorems/c091c5b9-174b-4942-997d-7ddf1d71ea64
-- title:
--   SNumbers: exists kolmogorov flag
-- statement:
--   **Kolmogorov flag.** From `γ < dₙ(S)`: vectors `x j` of the unit ball and
--   subspaces `V j` containing every earlier image `S (x k)`, `k < j`, with
--   `‖S (x j) + w‖ > γ` for all `w ∈ V j`. Each `V j` is the span of the images
--   chosen so far, of dimension at most `n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L407-L456
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L407-L456

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

theorem SNumbers.exists_kolmogorov_flag (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ}
    (hγd : γ < kolmogorovNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (V : Fin m → Submodule 𝕜 Y),
      (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j k : Fin m, k < j → S (x k) ∈ V j) ∧
      (∀ (j : Fin m) (w : Y), w ∈ V j → γ < ‖S (x j) + w‖) := by sorry
