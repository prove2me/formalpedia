-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:30.027036+00:00
-- url     : https://prove2.me/theorems/64bb3378-f711-4802-a86e-137aff15b652
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const psum At mul 5fb3aa7ed198: P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const psum At mul 5fb3aa7ed198
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const psum At mul 5fb3aa7ed198 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Eq dd Const psum At mul 5fb3aa7ed198 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L120-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L120-L137

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198 (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagEq».«ddConst_psumAt_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
