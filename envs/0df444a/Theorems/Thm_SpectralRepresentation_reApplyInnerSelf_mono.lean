-- Prove2me | Theorems.Thm_SpectralRepresentation_reApplyInnerSelf_mono
-- name    : SpectralRepresentation.reApplyInnerSelf_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:21.404016+00:00
-- url     : https://prove2.me/theorems/95cd6916-52ab-4fbd-be0b-093ff7037ddc
-- title:
--   Spectral Representation: re Apply Inner Self mono
-- statement:
--   The map `B ↦ re⟪B x, x⟫` is monotone for the Loewner order.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L89-L94
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L89-L94

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
omit [CompleteSpace H] [Nontrivial H]

theorem SpectralRepresentation.reApplyInnerSelf_mono {B C : H →L[ℂ] H} (h : B ≤ C) (x : H) :
    B.reApplyInnerSelf x ≤ C.reApplyInnerSelf x := by sorry
