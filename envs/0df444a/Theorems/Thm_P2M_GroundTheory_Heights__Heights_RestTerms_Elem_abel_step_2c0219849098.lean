-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:56.171847+00:00
-- url     : https://prove2.me/theorems/15f6fa02-6989-4b95-aec1-a838fd5e13dc
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem abel step 2c0219849098: P2 M Ground Theory Heights  Heights Rest Terms Elem abel step 2c0219849098
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem abel step 2c0219849098 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem abel step 2c0219849098 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L48-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L48-L111

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098 (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«abel_step» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_abel_step_2c0219849098
