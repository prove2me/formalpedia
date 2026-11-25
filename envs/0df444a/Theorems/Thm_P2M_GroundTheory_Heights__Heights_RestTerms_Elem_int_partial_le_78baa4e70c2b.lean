-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:45.614703+00:00
-- url     : https://prove2.me/theorems/0efa90bd-2328-53a6-87b2-6308bc335c75
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem int partial le 78baa4e70c2b: P2 M Ground Theory Heights  Heights Rest Terms Elem int partial le 78baa4e70c2b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem int partial le 78baa4e70c2b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem int partial le 78baa4e70c2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L261-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L261-L292

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b (B₀ : ℝ) (hB : 16 ≤ B₀) (K : ℕ) :
    ∑ m ∈ range K, intWeight B₀ m ≤ 2 * (1 + Real.log B₀) / B₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«int_partial_le» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_int_partial_le_78baa4e70c2b
