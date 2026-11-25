-- Prove2me | Theorems.Thm_SNumbers_norm_signedSum_single_le_one
-- name    : SNumbers.norm_signedSum_single_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:41.025556+00:00
-- url     : https://prove2.me/theorems/a4d4c15a-9edf-4b97-a719-ffcb5a9ccaf9
-- title:
--   SNumbers: norm signed Sum single le one
-- statement:
--   Signed sums of the unit vectors of `ℓ_∞` are contained in the unit ball.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L181-L185
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L181-L185

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*} [DecidableEq ι]

theorem SNumbers.norm_signedSum_single_le_one (S J : Finset ι) :
    ‖signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J‖ ≤ 1 := by sorry
