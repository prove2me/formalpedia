-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7
-- name    : P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:58.063836+00:00
-- url     : https://prove2.me/theorems/2e3aaa79-c85f-4c30-9b2e-6b4b02e0463e
-- title:
--   P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   symm to Lp df79e3edb4b7: P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   symm to Lp df79e3edb4b7
-- statement:
--   The P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   symm to Lp df79e3edb4b7 construction uses the P2 M Ground Theory Automorphic Sobolev Sobolev Space bessel   symm to Lp df79e3edb4b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L511-L520
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L511-L520

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
variable {m : E → ℂ} {C s t : ℝ}
open GroundTheory.Automorphic.Sobolev.SobolevSpace
variable {s : ℝ}

theorem P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7 (ψ : 𝓢(E, F)) :
    (besselₗᵢ s).symm (ψ.toLp 2) =
      ofSchwartz s (SchwartzMap.fourierMultiplierCLM F (weight (-s)) ψ) := by sorry

alias «GroundTheory».«Automorphic».«Sobolev».«SobolevSpace».«besselₗᵢ_symm_toLp» := P2M_GroundTheory_Automorphic_Sobolev_SobolevSpace_bessel___symm_toLp_df79e3edb4b7
