-- Prove2me | Theorems.Thm_SNumbers_totallyBounded_of_tendsto_kolmogorovNumber
-- name    : SNumbers.totallyBounded_of_tendsto_kolmogorovNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:49:55.514796+00:00
-- url     : https://prove2.me/theorems/89283611-763a-4484-a232-f3505e2c4f2b
-- title:
--   SNumbers: totally Bounded of tendsto kolmogorov Number
-- statement:
--   If `dₙ(S) → 0` then `S(B_X)` is totally bounded.
--
--   Given `η > 0`, choose `V` of dimension `≤ n` with `‖π_V ∘ S‖ < η/3`. Every
--   `S x` with `‖x‖ ≤ 1` is then within `η/3` of a point of `V` of norm at most
--   `‖S‖ + η/3`; that bounded piece of the finite-dimensional space `V` is compact,
--   so a finite `η/3`-net of it turns into a finite `η`-net of `S(B_X)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L176-L226
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L176-L226

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

theorem SNumbers.totallyBounded_of_tendsto_kolmogorovNumber {S : X →L[𝕜] Y}
    (hS : Tendsto (kolmogorovNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
