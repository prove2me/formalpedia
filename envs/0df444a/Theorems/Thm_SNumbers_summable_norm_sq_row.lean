-- Prove2me | Theorems.Thm_SNumbers_summable_norm_sq_row
-- name    : SNumbers.summable_norm_sq_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:25:39.70451+00:00
-- url     : https://prove2.me/theorems/e45565d0-56d4-482b-a3f6-6f57d734c28d
-- title:
--   SNumbers: summable norm sq row
-- statement:
--   Over the index set `ℕ`, the row bound makes `∑_j ‖w_j‖²` a convergent
--   series (its partial sums are nonnegative and bounded by `‖A‖²`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L271-L275
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L271-L275

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

theorem SNumbers.summable_norm_sq_row (A : H →L[𝕜] lp (fun _ : ℕ => 𝕜) 1) {w : ℕ → H}
    (hw : ∀ (j : ℕ) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) :
    Summable fun j => ‖w j‖ ^ 2 := by sorry
