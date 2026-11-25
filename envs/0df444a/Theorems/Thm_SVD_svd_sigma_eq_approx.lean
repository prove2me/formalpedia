-- Prove2me | Theorems.Thm_SVD_svd_sigma_eq_approx
-- name    : SVD.svd_sigma_eq_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:03:25.470827+00:00
-- url     : https://prove2.me/theorems/0c1bbfff-4f82-5aa9-8b15-cf7e749da5ee
-- title:
--   SVD: svd sigma eq approx
-- statement:
--   **Eckart–Young.** From any SVD of `S` (`OrthonormalOrZero` singular vectors
--   with the nonzero-σ tie, and the `HasSum` Schmidt expansion), the `m`-th singular
--   value equals the `m`-th approximation number: `σ m = aₘ(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1081-L1157
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L1081-L1157

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
omit [CompleteSpace H₁] [CompleteSpace H₂]

theorem SVD.svd_sigma_eq_approx {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁}
    {v : ℕ → H₂} (hσ0 : ∀ k, 0 ≤ σ k) (hσanti : Antitone σ) (hu : OrthonormalOrZero 𝕜 u)
    (hv : OrthonormalOrZero 𝕜 v) (hut : ∀ k, σ k ≠ 0 → u k ≠ 0) (hvt : ∀ k, σ k ≠ 0 → v k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (m : ℕ) :
    σ m = SNumbers.approximationNumber S m := by sorry
