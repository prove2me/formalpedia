-- Prove2me | Theorems.Thm_SNumbers_tendsto_kolmogorovNumber_of_isCompactOperator
-- name    : SNumbers.tendsto_kolmogorovNumber_of_isCompactOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:08:43.87427+00:00
-- url     : https://prove2.me/theorems/4b0c2e3e-12bd-5dc3-9449-c906d553e926
-- title:
--   SNumbers: tendsto kolmogorov Number of is Compact Operator
-- statement:
--   A compact operator has Kolmogorov numbers tending to zero.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L237-L240
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L237-L240

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

theorem SNumbers.tendsto_kolmogorovNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) : Tendsto (kolmogorovNumber S) atTop (𝓝 0) := by sorry
