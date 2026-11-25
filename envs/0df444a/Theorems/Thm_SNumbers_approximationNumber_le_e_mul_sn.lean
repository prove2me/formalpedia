-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_e_mul_sn
-- name    : SNumbers.approximationNumber_le_e_mul_sn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:38:08.746228+00:00
-- url     : https://prove2.me/theorems/c6f95c89-006d-408e-8d73-106cab2d3b8b
-- title:
--   SNumbers: approximation Number le e mul sn
-- statement:
--   **`aₙ(S) ≤ e·(n+1)·sₙ(S)` for every s-number sequence `s`**, since the
--   Hilbert numbers are the smallest s-number sequence (`hilbertNumber_le_sn`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L907-L911
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L907-L911

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

theorem SNumbers.approximationNumber_le_e_mul_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ Real.exp 1 * ((n : ℝ) + 1) * s S n := by sorry
