-- Prove2me | Theorems.Thm_SNumbers_project_singularValues_eq
-- name    : SNumbers.project_singularValues_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:13:57.242601+00:00
-- url     : https://prove2.me/theorems/a4a91c19-b182-4470-9437-a92bb37156cd
-- title:
--   SNumbers: project singular Values eq
-- statement:
--   **`aₙ(S) = σₙ(S)`: the SVD's singular values are Mathlib's.** `S` is compact
--   (finite-dimensional domain), so the SVD applies and `svd_sigma_eq_approx`
--   reduces the goal to `singularValues S n = σ n`. Mathlib defines
--   `singularValues` as `√` of the antitone `eigenvalues` of `S* ∘ S`, and
--   `svd_eigenvalues_eq_sq` shows those eigenvalues are exactly `i ↦ σᵢ²`; for
--   `n < finrank` this gives `singularValues n = √(σₙ²) = σₙ`, and for
--   `n ≥ finrank` both sides vanish (`svd_sigma_eq_zero_of_finrank_le`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/SingularValuesFinDim.lean#L354-L377
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/SingularValuesFinDim.lean#L354-L377

module
public import Definitions.Def_SNumbers_Uniqueness
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_SingularValuesFinDim
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [FiniteDimensional 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [FiniteDimensional 𝕜 H₂]
variable [Nontrivial H₁] [Nontrivial H₂]
omit [Nontrivial H₁] [Nontrivial H₂]

theorem SNumbers.project_singularValues_eq (S : H₁ →L[𝕜] H₂) (n : ℕ) :
    (S : H₁ →ₗ[𝕜] H₂).singularValues n = approximationNumber S n := by sorry
