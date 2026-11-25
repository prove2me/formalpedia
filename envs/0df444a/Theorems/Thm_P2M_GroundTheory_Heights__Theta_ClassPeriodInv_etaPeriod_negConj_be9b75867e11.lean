-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:07.281031+00:00
-- url     : https://prove2.me/theorems/c960a254-0ef0-4708-8e76-d38810011679
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv eta Period neg Conj be9b75867e11: P2 M Ground Theory Heights  Theta Class Period Inv eta Period neg Conj be9b75867e11
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv eta Period neg Conj be9b75867e11 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv eta Period neg Conj be9b75867e11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L256-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L256-L257

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
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
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11 (τ : ℍ) : etaPeriod (negConj τ) = etaPeriod τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«etaPeriod_negConj» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11
