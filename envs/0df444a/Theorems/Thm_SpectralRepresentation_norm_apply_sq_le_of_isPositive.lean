-- Prove2me | Theorems.Thm_SpectralRepresentation_norm_apply_sq_le_of_isPositive
-- name    : SpectralRepresentation.norm_apply_sq_le_of_isPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:33:27.114603+00:00
-- url     : https://prove2.me/theorems/ad047227-a336-4a2d-bc8d-3f7c395b6f92
-- title:
--   Spectral Representation: norm apply sq le of is Positive
-- statement:
--   **Cauchy estimate for positive operators.** For `A` positive,
--   `‖A x‖² ≤ ‖A‖ · re⟪A x, x⟫`. This powers the strong-operator monotone
--   convergence of positive operators.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L58-L77
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L58-L77

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

theorem SpectralRepresentation.norm_apply_sq_le_of_isPositive {A : H →L[ℂ] H} (hA : A.IsPositive) (x : H) :
    ‖A x‖ ^ 2 ≤ ‖A‖ * RCLike.re (⟪A x, x⟫_ℂ) := by sorry
