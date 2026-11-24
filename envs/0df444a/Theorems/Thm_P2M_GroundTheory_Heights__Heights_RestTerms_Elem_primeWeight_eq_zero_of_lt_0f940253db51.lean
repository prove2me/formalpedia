-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:02.162873+00:00
-- url     : https://prove2.me/theorems/31fed352-65a1-404a-9449-f6fc93624b3c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem prime Weight eq zero of lt 0f940253db51: P2 M Ground Theory Heights  Heights Rest Terms Elem prime Weight eq zero of lt 0f940253db51
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem prime Weight eq zero of lt 0f940253db51 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem prime Weight eq zero of lt 0f940253db51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L38-L46

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51 (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«primeWeight_eq_zero_of_lt» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_primeWeight_eq_zero_of_lt_0f940253db51
