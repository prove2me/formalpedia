-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:35.659886+00:00
-- url     : https://prove2.me/theorems/1e6285d9-e2a2-4ffd-a003-179d2db7cc88
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv eq of le of abs Norm eq 88c19db2ed55: P2 M Ground Theory Heights  Theta Class Period Inv eq of le of abs Norm eq 88c19db2ed55
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv eq of le of abs Norm eq 88c19db2ed55 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv eq of le of abs Norm eq 88c19db2ed55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L57-L64

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55 {J J' : Ideal (𝓞 K)} (h : J' ≤ J) (hn : Ideal.absNorm J' = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : J' = J := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«eq_of_le_of_absNorm_eq» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_eq_of_le_of_absNorm_eq_88c19db2ed55
