-- Prove2me | Theorems.Thm_SNumbers_tendsto_gelfandNumber_of_totallyBounded
-- name    : SNumbers.tendsto_gelfandNumber_of_totallyBounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:49:59.747936+00:00
-- url     : https://prove2.me/theorems/0852b463-5e15-4850-8304-a3b768ec19ed
-- title:
--   SNumbers: tendsto gelfand Number of totally Bounded
-- statement:
--   If `S(B_X)` is totally bounded then `cₙ(S) → 0`: a finite `ε/3`-net with `k`
--   points bounds `c_k(S)` by `2ε/3`, and `cₙ` is antitone.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L271-L286
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L271-L286

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

theorem SNumbers.tendsto_gelfandNumber_of_totallyBounded {S : X →L[𝕜] Y}
    (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) := by sorry
