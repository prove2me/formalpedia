-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:06.131613+00:00
-- url     : https://prove2.me/theorems/d3fda98c-248e-4ae8-b36f-ff174d4dfa18
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem phi T nonneg 7a19d717162f: P2 M Ground Theory Heights  Heights Rest Terms Elem phi T nonneg 7a19d717162f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem phi T nonneg 7a19d717162f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem phi T nonneg 7a19d717162f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L180-L183

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f {t : ℝ} (ht : 1 ≤ t) : 0 ≤ phiT t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«phiT_nonneg» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_phiT_nonneg_7a19d717162f
