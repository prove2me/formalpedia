-- Prove2me | Theorems.Thm_SpectralRepresentation_stepDown_eq_one
-- name    : SpectralRepresentation.stepDown_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:17:34.065295+00:00
-- url     : https://prove2.me/theorems/a806ff91-1b1d-49f2-b376-2e2439392b89
-- title:
--   Spectral Representation: step Down eq one
-- statement:
--   Above the threshold the approximation is exactly `1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L58-L61
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L58-L61

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

theorem SpectralRepresentation.stepDown_eq_one (t : ℝ) (n : ℕ) {s : ℝ} (hs : t ≤ s) : stepDown t n s = 1 := by sorry
