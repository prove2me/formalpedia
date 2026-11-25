-- Prove2me | Theorems.Thm_SpectralRepresentation_cfc_comm_of_comm
-- name    : SpectralRepresentation.cfc_comm_of_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:16:39.868623+00:00
-- url     : https://prove2.me/theorems/14a7bbae-7554-4e28-bb4a-0f33bfd4c1e6
-- title:
--   Spectral Representation: cfc comm of comm
-- statement:
--   A continuous `ℝ`-linear map `J` commuting with a self-adjoint `P` commutes with `cfc g P`
--   for every continuous `g`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L142-L146
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L142-L146

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

theorem SpectralRepresentation.cfc_comm_of_comm {P : H₁ →L[ℂ] H₁} (hP : IsSelfAdjoint P) (J : H₁ →L[ℝ] H₁)
    (hJP : ∀ x, J (P x) = P (J x)) {g : ℝ → ℝ} (hg : Continuous g) (x : H₁) :
    J (cfc g P x) = cfc g P (J x) := by sorry
