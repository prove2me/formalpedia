-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:04:55.533943+00:00
-- url     : https://prove2.me/theorems/57d10efc-25e9-5fdc-b6b8-79323fdd0de1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One sum update sub one 1c80aec9c4ac: P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One sum update sub one 1c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One sum update sub one 1c80aec9c4ac construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One sum update sub one 1c80aec9c4ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfMonomialPsumOne.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfMonomialPsumOne.lean#L11-L15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfMonomialPsumOne
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
open MvPolynomial Finset Comb
open GroundTheory.Heights₂.Heights.RestTerms.CombCfMonomialPsumOne

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac {m : ℕ} (l : Fin m → ℕ) (i : Fin m) (h : 1 ≤ l i) :
    ∑ j, Function.update l i (l i - 1) j + 1 = ∑ j, l j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombCfMonomialPsumOne».«sum_update_sub_one» := P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac
