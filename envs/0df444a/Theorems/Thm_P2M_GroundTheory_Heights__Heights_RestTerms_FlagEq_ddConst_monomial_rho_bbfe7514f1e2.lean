-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:39.446432+00:00
-- url     : https://prove2.me/theorems/89e8140e-aaae-52f4-8afb-26f9ce066cf0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const monomial rho bbfe7514f1e2: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const monomial rho bbfe7514f1e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const monomial rho bbfe7514f1e2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const monomial rho bbfe7514f1e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L139-L144

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2 (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«ddConst_monomial_rho» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_monomial_rho_bbfe7514f1e2
