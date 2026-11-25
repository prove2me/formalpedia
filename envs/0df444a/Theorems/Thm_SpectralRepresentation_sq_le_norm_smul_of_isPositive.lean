-- Prove2me | Theorems.Thm_SpectralRepresentation_sq_le_norm_smul_of_isPositive
-- name    : SpectralRepresentation.sq_le_norm_smul_of_isPositive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:22.417867+00:00
-- url     : https://prove2.me/theorems/66af2322-a2ac-405d-b115-d08512b7f201
-- title:
--   Spectral Representation: sq le norm smul of is Positive
-- statement:
--   For a positive operator `A`, `A² ≤ ‖A‖ • A`. On the spectrum `[0, ‖A‖]`
--   one has `t² ≤ ‖A‖ · t`, and the continuous functional calculus transfers this
--   pointwise inequality to the operator order.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L38-L53
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L38-L53

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

theorem SpectralRepresentation.sq_le_norm_smul_of_isPositive {A : H →L[ℂ] H} (hA : A.IsPositive) :
    A ^ 2 ≤ (‖A‖ : ℝ) • A := by sorry
