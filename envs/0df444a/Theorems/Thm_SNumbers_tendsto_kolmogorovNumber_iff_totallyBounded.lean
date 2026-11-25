-- Prove2me | Theorems.Thm_SNumbers_tendsto_kolmogorovNumber_iff_totallyBounded
-- name    : SNumbers.tendsto_kolmogorovNumber_iff_totallyBounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:23:59.589687+00:00
-- url     : https://prove2.me/theorems/324b79b7-1b2f-43ed-9100-55cf81c37288
-- title:
--   SNumbers: tendsto kolmogorov Number iff totally Bounded
-- statement:
--   **`dₙ(S) → 0` characterises total boundedness of `S(B_X)`.** No completeness
--   assumption is needed.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L230-L234
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L230-L234

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

theorem SNumbers.tendsto_kolmogorovNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (kolmogorovNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
