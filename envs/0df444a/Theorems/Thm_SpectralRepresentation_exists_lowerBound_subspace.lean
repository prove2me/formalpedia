-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_lowerBound_subspace
-- name    : SpectralRepresentation.exists_lowerBound_subspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:19.925691+00:00
-- url     : https://prove2.me/theorems/3b636b56-d32c-4012-984e-d415de020c41
-- title:
--   Spectral Representation: exists lower Bound subspace
-- statement:
--   **(★) Lower-bound subspace.** For `0 ≤ c < aₙ(S)` there is an `(n+1)`-dimensional subspace
--   `M ⊆ H₁` on which `S` is bounded below by `c`. Take the spectral projection `E` of `S*S` at
--   threshold `c`; its range has dimension `≥ n+1`, and `S` is bounded below by `c` there.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Representation.lean#L94-L141
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Representation.lean#L94-L141

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_BasicResults_Spectral_RealProjection
public import Definitions.Def_BasicResults_Spectral_Representation
set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap SNumbers.Complexification RCLike
universe u
open SpectralRepresentation
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

theorem SpectralRepresentation.exists_lowerBound_subspace
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < SNumbers.approximationNumber S n) :
    ∃ M : Submodule 𝕜 H₁, FiniteDimensional 𝕜 M ∧
      Module.finrank 𝕜 M = n + 1 ∧
      ∀ x ∈ M, c * ‖x‖ ≤ ‖S x‖ := by sorry
