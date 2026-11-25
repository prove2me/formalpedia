-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_eq_zero_of_lt_04912f758c1d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_eq_zero_of_lt_04912f758c1d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:12.414533+00:00
-- url     : https://prove2.me/theorems/da3646f7-6133-5439-aceb-9bdd0c736cd0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Out eq zero of lt 04912f758c1d: P2 M Ground Theory Heights  Heights Rest Terms Top block Out eq zero of lt 04912f758c1d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Out eq zero of lt 04912f758c1d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Out eq zero of lt 04912f758c1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L379-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L379-L387

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_eq_zero_of_lt_04912f758c1d (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ)
    (h : q + m < r * a) : blockOut r a c κ q m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockOut_eq_zero_of_lt» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockOut_eq_zero_of_lt_04912f758c1d
