-- Prove2me | Theorems.Thm_SpectralRepresentation_stepDown_antitone
-- name    : SpectralRepresentation.stepDown_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:16:04.006252+00:00
-- url     : https://prove2.me/theorems/7e176658-e5c9-4f5e-9865-fa13094d6356
-- title:
--   Spectral Representation: step Down antitone
-- statement:
--   The family is antitone in `n`: a larger `n` gives a steeper ramp, hence a
--   smaller value below the threshold (and `1` above).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L65-L73
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L65-L73

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

theorem SpectralRepresentation.stepDown_antitone (t s : ℝ) : Antitone (fun n => stepDown t n s) := by sorry
