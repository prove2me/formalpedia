-- Prove2me | Theorems.Thm_SNumbers_signedSum_single_coord
-- name    : SNumbers.signedSum_single_coord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:25:33.591438+00:00
-- url     : https://prove2.me/theorems/33ff5ded-c5d9-4230-a9fd-f186aebb18df
-- title:
--   SNumbers: signed Sum single coord
-- statement:
--   The coordinates of a signed sum of unit vectors of `ℓ_∞` are `0` and `±1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L165-L178
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L165-L178

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

theorem SNumbers.signedSum_single_coord (S J : Finset ι) (i : ι) :
    (signedSum (fun j => lp.single (E := fun _ : ι => 𝕜) ∞ j (1 : 𝕜)) S J) i
      = if i ∈ J then (if i ∈ S then (1 : 𝕜) else -1) else 0 := by sorry
