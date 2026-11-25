-- Prove2me | Theorems.Thm_SNumbers_tendsto_gelfandNumber_of_isCompactOperator
-- name    : SNumbers.tendsto_gelfandNumber_of_isCompactOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:11:30.959247+00:00
-- url     : https://prove2.me/theorems/57442521-4443-4768-b9ca-96f379cc15c8
-- title:
--   SNumbers: tendsto gelfand Number of is Compact Operator
-- statement:
--   A compact operator has Gelfand numbers tending to zero.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L394-L397
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L394-L397

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

theorem SNumbers.tendsto_gelfandNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) : Tendsto (gelfandNumber S) atTop (𝓝 0) := by sorry
