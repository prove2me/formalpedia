-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:20.161796+00:00
-- url     : https://prove2.me/theorems/e8f40e5d-b4e4-4384-82f1-ffebd660a7bd
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const eq c1a45b54fd72: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const eq c1a45b54fd72
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const eq c1a45b54fd72 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const eq c1a45b54fd72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L52-L55

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
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72 (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * coeff (stairExp f (j + k) w) G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«ddConst_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_eq_c1a45b54fd72
