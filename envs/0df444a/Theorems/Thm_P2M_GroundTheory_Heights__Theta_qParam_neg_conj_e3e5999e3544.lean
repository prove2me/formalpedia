-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544
-- name    : P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:01.591722+00:00
-- url     : https://prove2.me/theorems/8bdeb4ab-f7cf-5a06-abe8-41c5cbf10926
-- title:
--   P2 M Ground Theory Heights  Theta q Param neg conj e3e5999e3544: P2 M Ground Theory Heights  Theta q Param neg conj e3e5999e3544
-- statement:
--   The P2 M Ground Theory Heights  Theta q Param neg conj e3e5999e3544 construction uses the P2 M Ground Theory Heights  Theta q Param neg conj e3e5999e3544 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaLogPeriodNegConjPf.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaLogPeriodNegConjPf.lean#L12-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularForm Complex
open scoped Real

theorem P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544 (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-(starRingEnd ℂ) z) =
      starRingEnd ℂ (Function.Periodic.qParam h z) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«qParam_neg_conj» := P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544
