-- Prove2me | Theorems.Thm_SVD_svd_sigma_le_mul_of_factorization
-- name    : SVD.svd_sigma_le_mul_of_factorization
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:07:52.965797+00:00
-- url     : https://prove2.me/theorems/d165e036-9bd4-401b-a7df-c1a143d89689
-- title:
--   SVD: svd sigma le mul of factorization
-- statement:
--   A single singular value of a factored operator is bounded by the norms of the
--   two factors evaluated at the corresponding singular vectors:
--   `σₖ ≤ ‖T₂* vₖ‖ · ‖T₁ uₖ‖`. Indeed `T uₖ = σₖ vₖ` with `‖vₖ‖ = 1` (or `σₖ = 0`),
--   so `σₖ = re ⟪vₖ, T uₖ⟫ = re ⟪T₂* vₖ, T₁ uₖ⟫`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1475-L1494
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1475-L1494

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
omit [CompleteSpace H₁]

theorem SVD.svd_sigma_le_mul_of_factorization {T : H₁ →L[𝕜] H₃} {T₁ : H₁ →L[𝕜] H₂}
    {T₂ : H₂ →L[𝕜] H₃} (hfact : T = T₂.comp T₁) {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₃}
    (hu : OrthonormalOrZero 𝕜 u) (hv : OrthonormalOrZero 𝕜 v)
    (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (T x)) (k : ℕ) :
    σ k ≤ ‖ContinuousLinearMap.adjoint T₂ (v k)‖ * ‖T₁ (u k)‖ := by sorry
