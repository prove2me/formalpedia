-- Prove2me | Theorems.Thm_SNumbers_detSet_nonempty
-- name    : SNumbers.detSet_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:36:33.583038+00:00
-- url     : https://prove2.me/theorems/dcb77f0b-1267-41a4-a63d-804805458014
-- title:
--   SNumbers: det Set nonempty
-- statement:
--   The admissible set is nonempty (take `A = 0`, `B = 0`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L155-L156
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/MaxDifference.lean#L155-L156

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

theorem SNumbers.detSet_nonempty (S : X →L[𝕜] Y) (k : ℕ) : (detSet S k).Nonempty := by sorry
