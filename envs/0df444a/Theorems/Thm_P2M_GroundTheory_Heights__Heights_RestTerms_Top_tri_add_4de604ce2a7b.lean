-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:52.982356+00:00
-- url     : https://prove2.me/theorems/4999b661-66f1-4619-9a71-e7bac98ece7e
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top tri add 4de604ce2a7b: P2 M Ground Theory Heights  Heights Rest Terms Top tri add 4de604ce2a7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top tri add 4de604ce2a7b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top tri add 4de604ce2a7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L17-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«tri_add» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_tri_add_4de604ce2a7b
