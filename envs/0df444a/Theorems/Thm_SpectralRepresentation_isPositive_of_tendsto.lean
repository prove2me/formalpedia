-- Prove2me | Theorems.Thm_SpectralRepresentation_isPositive_of_tendsto
-- name    : SpectralRepresentation.isPositive_of_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:14:01.849016+00:00
-- url     : https://prove2.me/theorems/3ae80bff-6393-5b93-b9b7-4360b9d96b63
-- title:
--   Spectral Representation: is Positive of tendsto
-- statement:
--   A strong limit of positive operators is positive.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L260-L268
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L260-L268

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

theorem SpectralRepresentation.isPositive_of_tendsto {T : ℕ → H →L[ℂ] H} {E : H →L[ℂ] H}
    (hpos : ∀ n, (T n).IsPositive)
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.IsPositive := by sorry
