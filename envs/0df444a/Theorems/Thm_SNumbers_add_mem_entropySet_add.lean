-- Prove2me | Theorems.Thm_SNumbers_add_mem_entropySet_add
-- name    : SNumbers.add_mem_entropySet_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:08.804797+00:00
-- url     : https://prove2.me/theorems/5ab86dd6-962f-418f-93b5-830486a049fb
-- title:
--   SNumbers: add mem entropy Set add
-- statement:
--   Covering step behind additivity: if `S(B_X)` is covered by `2 ^ n` balls
--   of radius `ε` with centres `y`, and `T(B_X)` by `2 ^ m` balls of radius `δ`
--   with centres `z`, then the `2 ^ (n + m)` sums `y + z` cover `(S + T)(B_X)`
--   with radius `ε + δ`, by the triangle inequality.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L232-L252
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L232-L252

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.add_mem_entropySet_add {S T : X →L[𝕜] Y} {n m : ℕ} {ε δ : ℝ}
    (hε : ε ∈ entropySet S n) (hδ : δ ∈ entropySet T m) :
    ε + δ ∈ entropySet (S + T) (n + m) := by sorry
