-- Prove2me | Theorems.Thm_SVD_sum_norm_sq_apply_le_of_rows
-- name    : SVD.sum_norm_sq_apply_le_of_rows
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:06:27.811816+00:00
-- url     : https://prove2.me/theorems/00d7c29a-8721-4395-bcfe-3a9d884bfd9a
-- title:
--   SVD: sum norm sq apply le of rows
-- statement:
--   **Bessel plus a row bound.** Suppose the operator `S` is described by a
--   family `w` of "rows", in the sense that `‖S x‖² = ∑ⱼ |⟪wⱼ, x⟫|²`, and that the
--   partial sums of `‖wⱼ‖²` are bounded by `c`. Then `∑ₖ ‖S uₖ‖² ≤ c` along every
--   orthonormal-or-zero family `u`.
--
--   This is the Hilbert–Schmidt estimate that
--   `mul_approximationNumber_le_of_factorization` needs for each of its two factors:
--   interchange the two summations (`hasSum_sum`), apply Bessel's inequality
--   (`OrthonormalOrZero.sum_inner_products_le`) for each fixed row, and finish with
--   the row bound.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1432-L1468
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1432-L1468

module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_BasicResults_Spectral_Representation
public import Definitions.Def_BasicResults_SVD
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal
open SVD
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable {H₃ : Type u}
variable [NormedAddCommGroup H₃] [InnerProductSpace 𝕜 H₃] [CompleteSpace H₃]
omit [CompleteSpace H₁] [CompleteSpace H₂]

theorem SVD.sum_norm_sq_apply_le_of_rows {S : H₁ →L[𝕜] H₂} {w : ℕ → H₁} {c : ℝ}
    (hS : ∀ x : H₁, ‖S x‖ ^ 2 = ∑' j, ‖(inner 𝕜 (w j) x : 𝕜)‖ ^ 2)
    (hc : ∀ J : Finset ℕ, ∑ j ∈ J, ‖w j‖ ^ 2 ≤ c)
    {u : ℕ → H₁} (hu : OrthonormalOrZero 𝕜 u) (s : Finset ℕ) :
    ∑ k ∈ s, ‖S (u k)‖ ^ 2 ≤ c := by sorry
