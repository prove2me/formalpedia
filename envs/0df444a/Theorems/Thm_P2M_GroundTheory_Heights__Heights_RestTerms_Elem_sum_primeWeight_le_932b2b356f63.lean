-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:13.587589+00:00
-- url     : https://prove2.me/theorems/30e54e1d-de62-478b-b87b-1c8c6eab46f1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem sum prime Weight le 932b2b356f63: P2 M Ground Theory Heights  Heights Rest Terms Elem sum prime Weight le 932b2b356f63
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem sum prime Weight le 932b2b356f63 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem sum prime Weight le 932b2b356f63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L23-L36

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63 (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«sum_primeWeight_le» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_sum_primeWeight_le_932b2b356f63
