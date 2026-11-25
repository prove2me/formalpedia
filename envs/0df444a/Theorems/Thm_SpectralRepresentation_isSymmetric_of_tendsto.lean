-- Prove2me | Theorems.Thm_SpectralRepresentation_isSymmetric_of_tendsto
-- name    : SpectralRepresentation.isSymmetric_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:34:51.635575+00:00
-- url     : https://prove2.me/theorems/76bfd981-5af9-4f0f-acd1-5117a81350e8
-- title:
--   Spectral Representation: is Symmetric of tendsto
-- statement:
--   A strong limit of symmetric operators is symmetric (`⟪E x, y⟫ = ⟪x, E y⟫`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L248-L255
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L248-L255

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap RCLike
open scoped InnerProductSpace
open SpectralRepresentation
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Nontrivial H]
open Filter Topology
omit [CompleteSpace H] [Nontrivial H]

theorem SpectralRepresentation.isSymmetric_of_tendsto {T : ℕ → H →L[ℂ] H} {E : H →L[ℂ] H}
    (hsymm : ∀ n, (T n : H →ₗ[ℂ] H).IsSymmetric)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : (E : H →ₗ[ℂ] H).IsSymmetric := by sorry
