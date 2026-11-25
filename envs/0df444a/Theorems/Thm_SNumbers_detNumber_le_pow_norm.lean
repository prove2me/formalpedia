-- Prove2me | Theorems.Thm_SNumbers_detNumber_le_pow_norm
-- name    : SNumbers.detNumber_le_pow_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T05:20:27.809883+00:00
-- url     : https://prove2.me/theorems/2d113da1-4e5e-4e3f-806f-98490121d5b0
-- title:
--   SNumbers: det Number le pow norm
-- statement:
--   `Δₖ(S) ≤ ‖S‖ᵏ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L229-L230
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L229-L230

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

theorem SNumbers.detNumber_le_pow_norm (S : X →L[𝕜] Y) (k : ℕ) : detNumber S k ≤ ‖S‖ ^ k := by sorry
