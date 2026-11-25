-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:54.269635+00:00
-- url     : https://prove2.me/theorems/9eefe49f-87af-45b7-a643-5d135a60fb9b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem int step 09746dc8c802: P2 M Ground Theory Heights  Heights Rest Terms Elem int step 09746dc8c802
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem int step 09746dc8c802 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem int step 09746dc8c802 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L223-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L223-L259

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PrimeWeightEqZeroOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802 (B₀ : ℝ) (hB : 16 ≤ B₀) (j : ℕ) :
    ∑ m ∈ range (⌊B₀⌋₊ + 1 + j), intWeight B₀ m ≤
      phiT (⌊B₀⌋₊ : ℝ) - phiT ((⌊B₀⌋₊ + j : ℕ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«int_step» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_step_09746dc8c802
