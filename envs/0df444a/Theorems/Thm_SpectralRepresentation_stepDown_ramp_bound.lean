-- Prove2me | Theorems.Thm_SpectralRepresentation_stepDown_ramp_bound
-- name    : SpectralRepresentation.stepDown_ramp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:15:50.812117+00:00
-- url     : https://prove2.me/theorems/69ec5bcc-ac5b-50a0-90fe-029bfb3d782a
-- title:
--   Spectral Representation: step Down ramp bound
-- statement:
--   **Uniform ramp estimate.** `(s - t) · stepDown t n` is within `1/(n+1)` of
--   `(s - t)⁺ = max (s - t) 0`, uniformly in `s`. This drives the norm convergence
--   `cfc ((s-t)·stepDownₙ) P → cfc (s-t)⁺ P` (no Dini theorem needed: the bound is
--   explicit).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L79-L95
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L79-L95

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

theorem SpectralRepresentation.stepDown_ramp_bound (t : ℝ) (n : ℕ) (s : ℝ) :
    |(s - t) * stepDown t n s - max (s - t) 0| ≤ ((n : ℝ) + 1)⁻¹ := by sorry
