-- Prove2me | Theorems.Thm_SVD_svd_apply_left
-- name    : SVD.svd_apply_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:04:01.227687+00:00
-- url     : https://prove2.me/theorems/edc47085-7fa6-4e5a-a304-87f73f5524df
-- title:
--   SVD: svd apply left
-- statement:
--   From the SVD data, `S uₖ = σₖ vₖ` (collapse the `HasSum` at `uₖ`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L960-L972
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L960-L972

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

theorem SVD.svd_apply_left {S : H₁ →L[𝕜] H₂} {σ : ℕ → ℝ} {u : ℕ → H₁} {v : ℕ → H₂}
    (hu : OrthonormalOrZero 𝕜 u) (htie : ∀ k, σ k ≠ 0 → u k ≠ 0)
    (hsum : ∀ x, HasSum (fun k => ((σ k : 𝕜) * inner 𝕜 (u k) x) • v k) (S x)) (k : ℕ) :
    S (u k) = (σ k : 𝕜) • v k := by sorry
