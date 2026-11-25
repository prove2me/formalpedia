-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_spectral_projection
-- name    : SpectralRepresentation.exists_spectral_projection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:57.719546+00:00
-- url     : https://prove2.me/theorems/96289b66-1eec-5478-96e7-da44fe51cd3d
-- title:
--   Spectral Representation: exists spectral projection
-- statement:
--   **Spectral projection of `S*S`, uniformly over any `RCLike` field.** Realify `H₁, H₂` to real
--   Hilbert spaces, take the real spectral projection, and lift it back to a `𝕜`-linear operator: the
--   lift is `𝕜`-linear because it commutes with scalar multiplication (the commutation conjunct of
--   `exists_spectral_projection_real`). The key sublemma `adjoint (S.restrictScalars ℝ) =
--   (adjoint S).restrictScalars ℝ` is proved inline.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Representation.lean#L57-L89
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Representation.lean#L57-L89

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

theorem SpectralRepresentation.exists_spectral_projection (S : H₁ →L[𝕜] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[𝕜] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c := by sorry
