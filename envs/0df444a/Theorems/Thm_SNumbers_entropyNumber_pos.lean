-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_pos
-- name    : SNumbers.entropyNumber_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:22:25.907013+00:00
-- url     : https://prove2.me/theorems/a2dd5105-4693-4ac2-ba50-df36a235ab26
-- title:
--   SNumbers: entropy Number pos
-- statement:
--   **The entropy numbers fail the rank axiom (S4)**: `eₙ(S) > 0` for every `S ≠ 0`.
--   For a unit vector `x` with `v = S x ≠ 0`, the `2ⁿ + 1` points `(k/2ⁿ) v`, `k ≤ 2ⁿ`, lie in
--   `S(B_X)` at mutual distance at least `‖v‖/2ⁿ`, so `eₙ(S) ≥ ‖v‖/2ⁿ⁺¹` by
--   `le_entropyNumber_of_separated`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L321-L382
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L321-L382

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

theorem SNumbers.entropyNumber_pos {S : X →L[𝕜] Y} (hS : S ≠ 0) (n : ℕ) : 0 < entropyNumber S n := by sorry
