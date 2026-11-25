-- Prove2me | Theorems.Thm_SNumbers_sum_norm_apply_le_norm_l1
-- name    : SNumbers.sum_norm_apply_le_norm_l1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:19:02.900371+00:00
-- url     : https://prove2.me/theorems/8542e280-2b4a-4d01-aac7-ba95b59a94e5
-- title:
--   SNumbers: sum norm apply le norm l1
-- statement:
--   Finite partial sums of the absolute values of the coordinates of an
--   `ℓ₁`-vector are bounded by its norm.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L220-L224
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L220-L224

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
omit [DecidableEq ι]

theorem SNumbers.sum_norm_apply_le_norm_l1 (f : lp (fun _ : ι => 𝕜) 1) (J : Finset ι) :
    ∑ j ∈ J, ‖f j‖ ≤ ‖f‖ := by sorry
