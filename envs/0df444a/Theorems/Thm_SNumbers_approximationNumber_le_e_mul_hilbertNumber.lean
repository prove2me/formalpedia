-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_e_mul_hilbertNumber
-- name    : SNumbers.approximationNumber_le_e_mul_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:01:49.396941+00:00
-- url     : https://prove2.me/theorems/c2802256-39af-5ba4-97ea-cea3115f738e
-- title:
--   SNumbers: approximation Number le e mul hilbert Number
-- statement:
--   **Maximal difference theorem.** `aₙ(S) ≤ e·(n+1)·hₙ(S)`: the
--   approximation numbers, the largest s-numbers, exceed the Hilbert numbers, the
--   smallest ones, by at most a factor linear in `n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L900-L903
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L900-L903

module
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_BasicResults_Determinant
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_MaxDifference
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open scoped Pointwise
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.approximationNumber_le_e_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * hilbertNumber S n := by sorry
