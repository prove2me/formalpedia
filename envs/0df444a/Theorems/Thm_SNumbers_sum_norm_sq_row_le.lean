-- Prove2me | Theorems.Thm_SNumbers_sum_norm_sq_row_le
-- name    : SNumbers.sum_norm_sq_row_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:09.696081+00:00
-- url     : https://prove2.me/theorems/edd600a9-fe17-5d96-979e-9177c0359f15
-- title:
--   SNumbers: sum norm sq row le
-- statement:
--   **Little Grothendieck inequality for `H → ℓ₁`.** If `w j` are the *rows* of
--   `A : H → ℓ₁`, i.e. `⟪w j, x⟫ = (A x) j` for all `x`, then
--   `∑_{j ∈ J} ‖w j‖² ≤ ‖A‖²` for every finite `J`.
--
--   This is the little Grothendieck bound applied to the adjoint of `A`, which maps
--   `ℓ_∞ = ℓ₁'` into `H`; formulating it via the rows avoids constructing the
--   adjoint. The signed sums are bounded here by
--   `re ⟪z, z⟫ = re (∑_j ε_j (A z)_j) ≤ ‖A z‖₁ ≤ ‖A‖ ‖z‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L234-L258
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/LittleGrothendieck.lean#L234-L258

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

theorem SNumbers.sum_norm_sq_row_le (A : H →L[𝕜] lp (fun _ : ι => 𝕜) 1) {w : ι → H}
    (hw : ∀ (j : ι) (x : H), (inner 𝕜 (w j) x : 𝕜) = A x j) (J : Finset ι) :
    ∑ j ∈ J, ‖w j‖ ^ 2 ≤ ‖A‖ ^ 2 := by sorry
