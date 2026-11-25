-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:32.928428+00:00
-- url     : https://prove2.me/theorems/17076eac-6b6a-5685-9e34-30d11b5a7aac
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top sum erase const 5c346ca9300d: P2 M Ground Theory Heights  Heights Rest Terms Top sum erase const 5c346ca9300d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top sum erase const 5c346ca9300d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top sum erase const 5c346ca9300d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L145-L148

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d (f : ℕ) (τ : Fin f) (x : ℕ) :
    ∑ _σ ∈ Finset.univ.erase τ, x = (f - 1) * x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«sum_erase_const» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_sum_erase_const_5c346ca9300d
