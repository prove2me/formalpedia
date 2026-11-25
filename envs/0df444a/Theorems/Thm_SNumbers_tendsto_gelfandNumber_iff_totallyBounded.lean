-- Prove2me | Theorems.Thm_SNumbers_tendsto_gelfandNumber_iff_totallyBounded
-- name    : SNumbers.tendsto_gelfandNumber_iff_totallyBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:24:04.098206+00:00
-- url     : https://prove2.me/theorems/18eee3d6-f10e-5c54-a717-9b2ce2313ced
-- title:
--   SNumbers: tendsto gelfand Number iff totally Bounded
-- statement:
--   **`cₙ(S) → 0` characterises total boundedness of `S(B_X)`.** No completeness
--   assumption is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L388-L391
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L388-L391

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

theorem SNumbers.tendsto_gelfandNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
