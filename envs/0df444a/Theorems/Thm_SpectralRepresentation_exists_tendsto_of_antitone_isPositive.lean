-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_tendsto_of_antitone_isPositive
-- name    : SpectralRepresentation.exists_tendsto_of_antitone_isPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:12:45.822903+00:00
-- url     : https://prove2.me/theorems/9fd9bd91-c742-56a9-8854-6f95fb06a075
-- title:
--   Spectral Representation: exists tendsto of antitone is Positive
-- statement:
--   **Strong-operator monotone convergence.** A pointwise-antitone sequence of
--   positive operators converges in the strong operator topology: for every `x`,
--   `fun n => T n x` converges. The proof shows the sequence is Cauchy, controlling
--   `‖T n x - T m x‖²` by `2‖T 0‖ · (re⟪T n x,x⟫ - re⟪T m x,x⟫)` (the Cauchy
--   estimate `norm_apply_sq_le_of_isPositive`), the latter being Cauchy as a bounded
--   antitone real sequence.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L103-L177
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L103-L177

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

theorem SpectralRepresentation.exists_tendsto_of_antitone_isPositive {T : ℕ → (H →L[ℂ] H)}
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) (x : H) :
    ∃ y, Tendsto (fun n => T n x) atTop (𝓝 y) := by sorry
