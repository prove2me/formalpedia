-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_spectral_projection_real
-- name    : SpectralRepresentation.exists_spectral_projection_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:17:06.6102+00:00
-- url     : https://prove2.me/theorems/6b7bbb2e-d77b-5ecf-82c3-edae5abf5a6e
-- title:
--   Spectral Representation: exists spectral projection real
-- statement:
--   **Spectral projection of `S*S` (over `ℝ`).** The real analogue of
--   `exists_spectral_projection_complex`, obtained by complexifying and restricting the conjugation-
--   invariant complex projection.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/RealProjection.lean#L43-L97
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/RealProjection.lean#L43-L97

module
public import Definitions.Def_BasicResults_Spectral_Complexification
public import Definitions.Def_BasicResults_Spectral_Projection
public import Definitions.Def_BasicResults_Spectral_RealProjection
set_option autoImplicit true
@[expose] public section
public section
open SNumbers.Complexification ContinuousLinearMap
open SpectralRepresentation
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

theorem SpectralRepresentation.exists_spectral_projection_real [Nontrivial H₁]
    (S : H₁ →L[ℝ] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[ℝ] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c ∧
        ∀ K : H₁ →L[ℝ] H₁, (∀ x, K (((adjoint S).comp S) x) = ((adjoint S).comp S) (K x)) →
          ∀ x, K (E x) = E (K x) := by sorry
