-- Prove2me | Theorems.Thm_SVD_OrthonormalOrZero_smul_inner_eq
-- name    : SVD.OrthonormalOrZero.smul_inner_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:07:03.078405+00:00
-- url     : https://prove2.me/theorems/61b5da55-b729-4b7e-97bd-4840ca22e973
-- title:
--   Orthonormal Or Zero: smul inner eq
-- statement:
--   The `σ`-weighted inner product of an orthonormal-or-zero family collapses
--   to a Kronecker delta: `σⱼ·⟪uⱼ, uₖ⟫ = δⱼₖ·σₖ`, given the tie `uₖ = 0 ↔ σₖ = 0`
--   (so that a zero vector carries a zero weight, and a nonzero one is unit).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L143-L154
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/SVD.lean#L143-L154

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

theorem SVD.OrthonormalOrZero.smul_inner_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {u : ℕ → H} (h : OrthonormalOrZero 𝕜 u) {σ : ℕ → ℝ}
    (htie : ∀ k, σ k ≠ 0 → u k ≠ 0) (j k : ℕ) :
    (σ j : 𝕜) * inner 𝕜 (u j) (u k) = if j = k then (σ k : 𝕜) else 0 := by sorry
