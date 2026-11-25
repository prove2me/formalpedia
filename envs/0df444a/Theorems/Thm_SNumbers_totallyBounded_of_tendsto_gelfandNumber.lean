-- Prove2me | Theorems.Thm_SNumbers_totallyBounded_of_tendsto_gelfandNumber
-- name    : SNumbers.totallyBounded_of_tendsto_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:50:40.297522+00:00
-- url     : https://prove2.me/theorems/1bafe3e4-ff44-444d-8a74-39a93ac96476
-- title:
--   SNumbers: totally Bounded of tendsto gelfand Number
-- statement:
--   If `cₙ(S) → 0` then `S(B_X)` is totally bounded.
--
--   Given `η > 0`, choose a closed `M` of finite codimension with `‖S|_M‖ < η/6`.
--   The image of `B_X` in the finite-dimensional quotient `X ⧸ M` is bounded, hence
--   totally bounded; pick a finite `δ`-net of it *inside the image* and lift the
--   centres to `u₁, …, u_N ∈ B_X`. For `‖x‖ ≤ 1` with `‖[x] - [uⱼ]‖ < δ` there is
--   `m ∈ M` with `‖(x - uⱼ) - m‖ < δ`, and (this is the point) `‖m‖ ≤ 2 + δ ≤ 3`
--   independently of the codimension. Hence
--   `‖S x - S uⱼ‖ ≤ ‖S m‖ + ‖S‖·δ < 3·(η/6) + η/2 = η`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L297-L384
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L297-L384

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

theorem SNumbers.totallyBounded_of_tendsto_gelfandNumber {S : X →L[𝕜] Y}
    (hS : Tendsto (gelfandNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by sorry
