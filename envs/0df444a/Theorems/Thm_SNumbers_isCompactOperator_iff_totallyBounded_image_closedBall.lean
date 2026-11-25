-- Prove2me | Theorems.Thm_SNumbers_isCompactOperator_iff_totallyBounded_image_closedBall
-- name    : SNumbers.isCompactOperator_iff_totallyBounded_image_closedBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:23:38.489081+00:00
-- url     : https://prove2.me/theorems/4ee1065a-2b40-4c38-85c8-e66cebc2c7dc
-- title:
--   SNumbers: is Compact Operator iff totally Bounded image closed Ball
-- statement:
--   For a complete target space, compactness of `S` is total boundedness of
--   `S(B_X)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L117-L121
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L117-L121

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

theorem SNumbers.isCompactOperator_iff_totallyBounded_image_closedBall [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
