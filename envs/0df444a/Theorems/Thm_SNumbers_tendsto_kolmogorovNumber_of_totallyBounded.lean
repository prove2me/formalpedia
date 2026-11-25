-- Prove2me | Theorems.Thm_SNumbers_tendsto_kolmogorovNumber_of_totallyBounded
-- name    : SNumbers.tendsto_kolmogorovNumber_of_totallyBounded
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:49:22.440677+00:00
-- url     : https://prove2.me/theorems/859143ba-e432-4ac0-aff2-85c31e3c17b4
-- title:
--   SNumbers: tendsto kolmogorov Number of totally Bounded
-- statement:
--   If `S(B_X)` is totally bounded then `dₙ(S) → 0`: a finite `ε/2`-net with `k`
--   points bounds `d_k(S)` by `ε/2`, and `dₙ` is antitone.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L154-L168
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/AddOns/Compact.lean#L154-L168

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

theorem SNumbers.tendsto_kolmogorovNumber_of_totallyBounded {S : X →L[𝕜] Y}
    (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    Tendsto (kolmogorovNumber S) atTop (𝓝 0) := by sorry
