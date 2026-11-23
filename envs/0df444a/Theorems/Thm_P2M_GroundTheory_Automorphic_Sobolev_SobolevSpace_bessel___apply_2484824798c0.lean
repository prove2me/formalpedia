-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0
-- name    : P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:08.298803+00:00
-- url     : https://prove2.me/theorems/0d7c4b36-362f-4436-8a70-57b30522c010
-- title:
--   P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   apply 2484824798c0: P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   apply 2484824798c0
-- statement:
--   The P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   apply 2484824798c0 construction uses the P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   apply 2484824798c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L115-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L115-L115

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}

theorem P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0 (u : SobolevSpace E F s) : besselₗᵢ s u = bessel s u := by sorry

alias «GroundTheory».«Automorphic».«Sobolev».«SobolevSpace».«besselₗᵢ_apply» := P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___apply_2484824798c0
