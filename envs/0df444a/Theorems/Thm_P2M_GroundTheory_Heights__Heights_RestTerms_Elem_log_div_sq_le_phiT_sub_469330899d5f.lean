-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:58.214814+00:00
-- url     : https://prove2.me/theorems/c46bd2cf-f1c9-40c7-a4d1-1e25375adb99
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Elem log div sq le phi T sub 469330899d5f: P2 M Ground Theory Heights  Heights Rest Terms Elem log div sq le phi T sub 469330899d5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Elem log div sq le phi T sub 469330899d5f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Elem log div sq le phi T sub 469330899d5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L185-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PrimeWeightEqZeroOfLt.lean#L185-L213

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f (x : ℝ) (hx : 3 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ phiT x - phiT (x + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Elem».«log_div_sq_le_phiT_sub» := P2M_GroundTheory_Heights__Heights_RestTerms_Elem_log_div_sq_le_phiT_sub_469330899d5f
