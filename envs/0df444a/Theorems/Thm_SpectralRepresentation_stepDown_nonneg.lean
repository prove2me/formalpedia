-- Prove2me | Theorems.Thm_SpectralRepresentation_stepDown_nonneg
-- name    : SpectralRepresentation.stepDown_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:36:00.446711+00:00
-- url     : https://prove2.me/theorems/9b40b713-52e4-4cc5-a7e7-a1d72cfc3a9b
-- title:
--   Spectral Representation: step Down nonneg
-- statement:
--   The Spectral Representation construction uses the step Down nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L51-L52
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Projection.lean#L51-L52

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

theorem SpectralRepresentation.stepDown_nonneg (t : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ stepDown t n s := by sorry
