-- Prove2me | Theorems.Thm_SNumbers_detNumber_succ_le_hilbertNumber_mul
-- name    : SNumbers.detNumber_succ_le_hilbertNumber_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:58:58.875179+00:00
-- url     : https://prove2.me/theorems/f2c1e7a3-708c-4436-b6e6-6d94265b4b0a
-- title:
--   SNumbers: det Number succ le hilbert Number mul
-- statement:
--   **Upper bound `Δₙ₊₁(S) ≤ hₙ(S)·Δₙ(S)`.** For every admissible pair for
--   `Δₙ₊₁` and `T := B∘S∘A`, split `|det T| = ∏_{k≤n} aₖ(T)` into the top `n`
--   factors (at most `Δₙ(S)`, by the compression bound) and the last factor
--   `aₙ(T) ≤ hₙ(S)`. This bounds **every** element of the supremum defining
--   `Δₙ₊₁(S)`, so no near-maximiser is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L376-L403
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L376-L403

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

theorem SNumbers.detNumber_succ_le_hilbertNumber_mul (S : X →L[𝕜] Y) (n : ℕ) :
    detNumber S (n + 1) ≤ hilbertNumber S n * detNumber S n := by sorry
