-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:10.356002+00:00
-- url     : https://prove2.me/theorems/30b3d9d4-3c29-4718-ba1d-b2df065c854b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const apply a09bce188ba1: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const apply a09bce188ba1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const apply a09bce188ba1 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const apply a09bce188ba1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L45-L50

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1 (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      coeff (rho f (j + k)) (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«ddConst_apply» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_apply_a09bce188ba1
