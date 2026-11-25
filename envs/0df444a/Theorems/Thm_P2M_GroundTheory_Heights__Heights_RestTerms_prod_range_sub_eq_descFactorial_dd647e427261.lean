-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_range_sub_eq_descFactorial_dd647e427261
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_prod_range_sub_eq_descFactorial_dd647e427261
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:16.998354+00:00
-- url     : https://prove2.me/theorems/7572ad10-23b6-4394-9b18-2deeeba5a087
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms prod range sub eq desc Factorial dd647e427261: P2 M Ground Theory Heights  Heights Rest Terms prod range sub eq desc Factorial dd647e427261
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms prod range sub eq desc Factorial dd647e427261 construction uses the P2 M Ground Theory Heights  Heights Rest Terms prod range sub eq desc Factorial dd647e427261 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_prod_range_sub_eq_descFactorial_dd647e427261 (n l : ℕ) :
    ∏ j ∈ Finset.range l, (n - j) = n.descFactorial l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«prod_range_sub_eq_descFactorial» := P2M_GroundTheory_Heights__Heights_RestTerms_prod_range_sub_eq_descFactorial_dd647e427261
