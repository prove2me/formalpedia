-- Prove2me | Theorems.Thm_SpectralRepresentation_exists_continuousLinearMap_tendsto
-- name    : SpectralRepresentation.exists_continuousLinearMap_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:13:18.860801+00:00
-- url     : https://prove2.me/theorems/13e8f5c8-9724-467e-95ff-4ea70c3c07c1
-- title:
--   Spectral Representation: exists continuous Linear Map tendsto
-- statement:
--   **The strong limit as a bounded operator.** A pointwise-antitone sequence of
--   positive operators has a continuous-linear strong limit `E`: `T n x → E x` for
--   every `x`, with `‖E‖ ≤ ‖T 0‖`.
--
--   The continuity of the limit is established here by hand, via the uniform bound
--   `‖T k‖ ≤ ‖T 0‖` and `LinearMap.mkContinuous`. Mathlib's
--   `continuousLinearMapOfTendsto` proves the same thing in general (a pointwise
--   limit of continuous linear maps along a countably generated filter is again
--   continuous), but it rests on Banach–Steinhaus, so using it would pull
--   `Mathlib.Analysis.LocallyConvex.Barrelled` into this file. Since the uniform
--   bound is available for free here, the elementary route is kept.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L191-L236
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/MonotoneConvergence.lean#L191-L236

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

theorem SpectralRepresentation.exists_continuousLinearMap_tendsto {T : ℕ → (H →L[ℂ] H)}
    (hpos : ∀ n, (T n).IsPositive) (hanti : Antitone T) :
    ∃ E : H →L[ℂ] H, ∀ x, Tendsto (fun n => T n x) atTop (𝓝 (E x)) := by sorry
