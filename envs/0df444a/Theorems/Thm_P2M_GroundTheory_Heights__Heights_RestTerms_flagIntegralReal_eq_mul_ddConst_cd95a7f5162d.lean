-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:30.579542+00:00
-- url     : https://prove2.me/theorems/4a5aaa57-70f6-4904-bcaf-a804fab87768
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real eq mul dd Const cd95a7f5162d: P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real eq mul dd Const cd95a7f5162d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real eq mul dd Const cd95a7f5162d construction uses the P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real eq mul dd Const cd95a7f5162d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L150-L152

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
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
open FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«flagIntegralReal_eq_mul_ddConst» := P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_eq_mul_ddConst_cd95a7f5162d
