-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Hk_LFamPos_hasSum_re__42147fd3e813
-- name    : P2M_GlobalTheory_Hk_LFamPos_hasSum_re__42147fd3e813
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:03.543444+00:00
-- url     : https://prove2.me/theorems/3aa82c27-3c51-4066-ab59-ad535e2a1d93
-- title:
--   P2 M Global Theory Hk LFam Pos has Sum re  42147fd3e813: P2 M Global Theory Hk LFam Pos has Sum re  42147fd3e813
-- statement:
--   The P2 M Global Theory Hk LFam Pos has Sum re  42147fd3e813 construction uses the P2 M Global Theory Hk LFam Pos has Sum re  42147fd3e813 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RayClassLFunctionFamilyLogDerivPositivity.lean#L42-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LFamPos

theorem P2M_GlobalTheory_Hk_LFamPos_hasSum_re__42147fd3e813 (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by sorry

alias «GlobalTheory».«Hk».«LFamPos».«hasSum_re₀» := P2M_GlobalTheory_Hk_LFamPos_hasSum_re__42147fd3e813
