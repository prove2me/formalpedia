-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_of_totallyBounded_image_closedBall
-- name    : SNumbers.isCompactOperator_of_totallyBounded_image_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:46:50.517627+00:00
-- url     : https://prove2.me/theorems/9914077c-0078-475f-a5b4-b7ec0e931816
-- title:
--   SNumbers: is Compact Operator of totally Bounded image closed Ball
-- statement:
--   Conversely, if `S(B_X)` is totally bounded and `Y` is complete, then `S` is
--   a compact operator: the closure of a totally bounded set is then compact.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L109-L113
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L109-L113

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
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem SNumbers.isCompactOperator_of_totallyBounded_image_closedBall [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    IsCompactOperator S := by sorry
