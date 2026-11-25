-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:05:17.986435+00:00
-- url     : https://prove2.me/theorems/46aca74f-15ea-5b09-9848-cc2da1ae0034
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One prod factorial update sub one 5ed83b2dd899: P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One prod facto
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One prod factorial update sub one 5ed83b2dd899 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb Cf Monomial Psum One prod factorial update sub one 5ed83b2dd899 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfMonomialPsumOne.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCfMonomialPsumOne.lean#L17-L32

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899 {m : ℕ} (l v : Fin m → ℕ) (i : Fin m) (hi : v i < l i) :
    (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) * ((l i - v i : ℕ) : ℚ) =
      ∏ j, ((l j - v j).factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«CombCfMonomialPsumOne».«prod_factorial_update_sub_one» := P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899
