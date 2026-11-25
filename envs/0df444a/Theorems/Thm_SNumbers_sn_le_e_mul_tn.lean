-- Prove2me | Theorems.Thm_SNumbers_sn_le_e_mul_tn
-- name    : SNumbers.sn_le_e_mul_tn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:02:06.45405+00:00
-- url     : https://prove2.me/theorems/8ae61bfd-af66-5f41-a136-b7080175831f
-- title:
--   SNumbers: sn le e mul tn
-- statement:
--   **Maximal difference theorem for arbitrary s-numbers.**
--   `sₙ(S) ≤ e·(n+1)·tₙ(S)`: any two s-number sequences differ at most by a
--   factor linear in `n`. Bound `s` by the largest s-numbers `aₙ`
--   (`sn_le_approximationNumber`) and then apply the theorem to `t`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L917-L921
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L917-L921

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

theorem SNumbers.sn_le_e_mul_tn {s t : Family 𝕜} (hs : IsSNumberSequence s)
    (ht : IsSNumberSequence t) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ Real.exp 1 * ((n : ℝ) + 1) * t S n := by sorry
