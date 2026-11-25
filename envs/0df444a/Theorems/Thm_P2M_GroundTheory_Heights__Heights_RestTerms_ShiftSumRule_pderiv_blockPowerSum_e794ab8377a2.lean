-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:03.067472+00:00
-- url     : https://prove2.me/theorems/10633969-7c50-54b9-a4c0-289a129a5b71
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule pderiv block Power Sum e794ab8377a2: P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule pderiv block Power Sum e794ab8377a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule pderiv block Power Sum e794ab8377a2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Shift Sum Rule pderiv block Power Sum e794ab8377a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PShiftSumRule.lean#L22-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PShiftSumRule
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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.ShiftSumRule

theorem P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2 (N k : ℕ) (i : Fin N) :
    pderiv ((0 : Fin 1), i) (blockPowerSum 1 N k 0) =
      (k : RootRing 1 N) * X ((0 : Fin 1), i) ^ (k - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«ShiftSumRule».«pderiv_blockPowerSum» := P2M_GroundTheory_Heights__Heights_RestTerms_ShiftSumRule_pderiv_blockPowerSum_e794ab8377a2
