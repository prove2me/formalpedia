-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:39.576816+00:00
-- url     : https://prove2.me/theorems/87ee72fd-ec5c-49ef-b3d7-853a92280765
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv exists conj aut b79dc8972092: P2 M Ground Theory Heights  Theta Class Period Inv exists conj aut b79dc8972092
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv exists conj aut b79dc8972092 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv exists conj aut b79dc8972092 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L17-L22

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092 (hK : finrank ℚ K = 2) (σ : K →+* ℂ) :
    ∃ g : K ≃ₐ[ℚ] K, ∀ x, σ (g x) = starRingEnd ℂ (σ x) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«exists_conj_aut» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_conj_aut_b79dc8972092
