-- Prove2me | Theorems.Thm_SNumbers_sn_le_two_e_mul_entropyNumber
-- name    : SNumbers.sn_le_two_e_mul_entropyNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:23:16.065817+00:00
-- url     : https://prove2.me/theorems/f0853f15-1c19-4e70-9e2b-1a896887d458
-- title:
--   SNumbers: sn le two e mul entropy Number
-- statement:
--   **Every s-number sequence is bounded by the entropy numbers**:
--   `sₙ(S) ≤ 2e·(n+1)·eₙ(S)`. The bound `sₙ ≤ e·(n+1)·tₙ` between any two s-number sequences
--   (`sn_le_e_mul_tn`), taken with `t` the Hilbert numbers, combined with the Hilbert-entropy
--   bound `hₙ ≤ 2·eₙ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L1003-L1012
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/EntropyBounds.lean#L1003-L1012

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

theorem SNumbers.sn_le_two_e_mul_entropyNumber {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ 2 * Real.exp 1 * ((n : ℝ) + 1) * entropyNumber S n := by sorry
