-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_le_approximationNumber
-- name    : SNumbers.gelfandNumber_le_approximationNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:05:41.478807+00:00
-- url     : https://prove2.me/theorems/3f5e7431-ea9a-5f26-a89c-dc2760ce4d63
-- title:
--   SNumbers: gelfand Number le approximation Number
-- statement:
--   `cₙ(S) ≤ aₙ(S)`: the Gelfand numbers are an s-number sequence, and the
--   approximation numbers are the largest one (`sn_le_approximationNumber`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L931-L933
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L931-L933

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

theorem SNumbers.gelfandNumber_le_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ approximationNumber S n := by sorry
