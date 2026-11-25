-- Prove2me | Theorems.Thm_SNumbers_detSet_bddAbove
-- name    : SNumbers.detSet_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:57:36.703912+00:00
-- url     : https://prove2.me/theorems/1837ccc5-972d-43ed-885b-7270e2a1617e
-- title:
--   SNumbers: det Set bdd Above
-- statement:
--   The admissible set is bounded above by `‖S‖ᵏ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L198-L199
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L198-L199

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

theorem SNumbers.detSet_bddAbove (S : X →L[𝕜] Y) (k : ℕ) : BddAbove (detSet S k) := by sorry
