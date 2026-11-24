-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_proof_d9ec121f6930
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_proof_d9ec121f6930
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:08.711933+00:00
-- url     : https://prove2.me/theorems/c3e40b7f-da31-4589-8ce2-c3605791057d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound proof d9ec121f6930: P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound proof d9ec121f6930
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound proof d9ec121f6930 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Other Factor Bound proof d9ec121f6930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorBound.lean#L83-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/POtherFactorBound.lean#L83-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_POtherFactorBound
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_proof_d9ec121f6930 (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«OtherFactorBound».«proof» := P2M_GroundTheory_Heights__Heights_RestTerms_OtherFactorBound_proof_d9ec121f6930
