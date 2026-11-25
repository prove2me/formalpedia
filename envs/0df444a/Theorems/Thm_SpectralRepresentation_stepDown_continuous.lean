-- Prove2me | Theorems.Thm_SpectralRepresentation_stepDown_continuous
-- name    : SpectralRepresentation.stepDown_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:35:50.421513+00:00
-- url     : https://prove2.me/theorems/4c0ba2ed-72d8-443b-af3f-48ff952ea64b
-- title:
--   Spectral Representation: step Down continuous
-- statement:
--   The Spectral Representation construction uses the step Down continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L48-L49
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L48-L49

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

theorem SpectralRepresentation.stepDown_continuous (t : ℝ) (n : ℕ) : Continuous (stepDown t n) := by sorry
