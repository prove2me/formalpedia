-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_of_tendsto_gelfandNumber
-- name    : SNumbers.isCompactOperator_of_tendsto_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:12:39.893201+00:00
-- url     : https://prove2.me/theorems/2361b2f6-90a0-4a25-825d-06ea8ed8fe92
-- title:
--   SNumbers: is Compact Operator of tendsto gelfand Number
-- statement:
--   Gelfand numbers tending to zero force compactness, provided the target space
--   is complete.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L401-L405
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L401-L405

module
public import Definitions.Def_AddOns_Approximable
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_SNumbers_EntropyBounds
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_AddOns_Compact
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.isCompactOperator_of_tendsto_gelfandNumber [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (gelfandNumber S) atTop (𝓝 0)) :
    IsCompactOperator S := by sorry
