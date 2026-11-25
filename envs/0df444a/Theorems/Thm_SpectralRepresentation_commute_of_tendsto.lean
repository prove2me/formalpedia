-- Prove2me | Theorems.Thm_SpectralRepresentation_commute_of_tendsto
-- name    : SpectralRepresentation.commute_of_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:14:28.272174+00:00
-- url     : https://prove2.me/theorems/02984fc6-1a21-42f3-bbb5-3e20db03cc61
-- title:
--   Spectral Representation: commute of tendsto
-- statement:
--   If every `T n` commutes with `P`, so does the strong limit `E`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L273-L282
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L273-L282

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

theorem SpectralRepresentation.commute_of_tendsto {T : ℕ → H →L[ℂ] H} {E P : H →L[ℂ] H}
    (hcomm : ∀ n, (T n).comp P = P.comp (T n))
    (hE : ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x))) : E.comp P = P.comp E := by sorry
