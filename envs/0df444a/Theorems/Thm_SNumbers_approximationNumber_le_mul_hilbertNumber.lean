-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_mul_hilbertNumber
-- name    : SNumbers.approximationNumber_le_mul_hilbertNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:00:26.213804+00:00
-- url     : https://prove2.me/theorems/a1155bcc-1d1a-5120-9f49-92853df727bc
-- title:
--   SNumbers: approximation Number le mul hilbert Number
-- statement:
--   **`aₙ(S) ≤ ((n+1)^{n+1}/nⁿ)·hₙ(S)`**, the maximal difference theorem
--   with the sharp form of the constant.
--   Chaining the growth lemma at `k = n` with the upper bound
--   `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)` gives
--
--     `(nⁿ/(n+1)^{n+1})·aₙ(S)·Δₙ(S) ≤ Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`,
--
--   and `Δₙ(S) > 0` may be cancelled.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L873-L895
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L873-L895

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

theorem SNumbers.approximationNumber_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n
      ≤ ((n : ℝ) + 1) ^ (n + 1) / (n : ℝ) ^ n * hilbertNumber S n := by sorry
