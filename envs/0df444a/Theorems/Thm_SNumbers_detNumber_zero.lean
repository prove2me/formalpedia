-- Prove2me | Theorems.Thm_SNumbers_detNumber_zero
-- name    : SNumbers.detNumber_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:06:05.608671+00:00
-- url     : https://prove2.me/theorems/22ef0166-ff2a-5c4c-9081-de857f4e1779
-- title:
--   SNumbers: det Number zero
-- statement:
--   **`Δ₀(S) = 1`.** Every endomorphism of the trivial space `ℓ₂⁰` has
--   determinant `1`, so the admissible set is exactly `{1}`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L214-L226
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L214-L226

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

theorem SNumbers.detNumber_zero (S : X →L[𝕜] Y) : detNumber S 0 = 1 := by sorry
