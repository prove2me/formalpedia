-- Prove2me | Theorems.Thm_SNumbers_norm_sq_eq_tsum_norm_sq
-- name    : SNumbers.norm_sq_eq_tsum_norm_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:19.475906+00:00
-- url     : https://prove2.me/theorems/24bf9252-cba9-41b7-a419-47146f83bec3
-- title:
--   SNumbers: norm sq eq tsum norm sq
-- statement:
--   The squared `ℓ₂`-norm is the sum of the squared coordinate norms.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L278-L282
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L278-L282

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

theorem SNumbers.norm_sq_eq_tsum_norm_sq {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : lp E 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by sorry
