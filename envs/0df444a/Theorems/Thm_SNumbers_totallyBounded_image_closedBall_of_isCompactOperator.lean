-- Prove2me | Theorems.Thm_SNumbers_totallyBounded_image_closedBall_of_isCompactOperator
-- name    : SNumbers.totallyBounded_image_closedBall_of_isCompactOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:42:36.435427+00:00
-- url     : https://prove2.me/theorems/5537fb79-678f-56a0-b1ab-dd1715857aba
-- title:
--   SNumbers: totally Bounded image closed Ball of is Compact Operator
-- statement:
--   A compact operator maps the closed unit ball to a totally bounded set.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L101-L105
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L101-L105

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

theorem SNumbers.totallyBounded_image_closedBall_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
