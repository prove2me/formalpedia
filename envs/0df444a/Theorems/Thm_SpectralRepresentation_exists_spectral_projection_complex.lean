-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_spectral_projection_complex
-- name    : SpectralRepresentation.exists_spectral_projection_complex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:16:41.386376+00:00
-- url     : https://prove2.me/theorems/fc2e338d-6331-472e-9ada-18fdeffdb68d
-- title:
--   Spectral Representation: exists spectral projection complex
-- statement:
--   **Spectral projection of `S*S` (over `ℂ`).**
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L149-L329
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L149-L329

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
open Filter Topology
open scoped InnerProductSpace
variable {H₁ H₂ : Type*}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

theorem SpectralRepresentation.exists_spectral_projection_complex [Nontrivial H₁]
    (S : H₁ →L[ℂ] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[ℂ] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c ∧
        ∀ J : H₁ →L[ℝ] H₁, (∀ x, J (((adjoint S).comp S) x) = ((adjoint S).comp S) (J x)) →
          ∀ x, J (E x) = E (J x) := by sorry
