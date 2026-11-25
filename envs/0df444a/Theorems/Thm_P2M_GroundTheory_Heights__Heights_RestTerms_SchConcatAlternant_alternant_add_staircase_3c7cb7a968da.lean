-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_add_staircase_3c7cb7a968da
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_add_staircase_3c7cb7a968da
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:37.069334+00:00
-- url     : https://prove2.me/theorems/785595e6-69cb-4b94-89c6-016bbec30a8f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant add staircase 3c7cb7a968da: P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant add staircase 3c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant add staircase 3c7cb7a968da construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant add staircase 3c7cb7a968da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchConcatAlternant.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchConcatAlternant.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatAlternant
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_add_staircase_3c7cb7a968da {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchConcatAlternant».«alternant_add_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_add_staircase_3c7cb7a968da
