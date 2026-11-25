-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:47.322978+00:00
-- url     : https://prove2.me/theorems/7cc3449e-ef4a-4c82-9616-7bf09ca13df3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem prime partial le 66a4bd05bbf2: P2 M Ground Theory Heights  Heights Rest Terms Elem prime partial le 66a4bd05bbf2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem prime partial le 66a4bd05bbf2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem prime partial le 66a4bd05bbf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L113-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L113-L147

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2 (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«prime_partial_le» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_prime_partial_le_66a4bd05bbf2
