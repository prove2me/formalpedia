-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_le_approximationNumber
-- name    : SNumbers.kolmogorovNumber_le_approximationNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:02:36.194006+00:00
-- url     : https://prove2.me/theorems/87fe5eb7-f56a-53df-aee9-8b2920ded8a9
-- title:
--   SNumbers: kolmogorov Number le approximation Number
-- statement:
--   `dₙ(S) ≤ aₙ(S)`: the Kolmogorov numbers are an s-number sequence, and the
--   approximation numbers are the largest one (`sn_le_approximationNumber`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L937-L939
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L937-L939

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

theorem SNumbers.kolmogorovNumber_le_approximationNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ approximationNumber S n := by sorry
