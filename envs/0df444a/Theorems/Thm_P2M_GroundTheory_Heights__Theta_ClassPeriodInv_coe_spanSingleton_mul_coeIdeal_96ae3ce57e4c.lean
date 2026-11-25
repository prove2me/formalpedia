-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:23.967+00:00
-- url     : https://prove2.me/theorems/46337bb6-5d8e-46fb-bd70-27b8ae0f0d86
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv coe span Singleton mul coe Ideal 96ae3ce57e4c: P2 M Ground Theory Heights  Theta Class Period Inv coe span Singleton mul coe Ideal 96ae3ce57e4c
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv coe span Singleton mul coe Ideal 96ae3ce57e4c construction uses the P2 M Ground Theory Heights  Theta Class Period Inv coe span Singleton mul coe Ideal 96ae3ce57e4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L93-L103

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c (c : K) (M : Ideal (𝓞 K)) :
    ((FractionalIdeal.spanSingleton (𝓞 K)⁰ c * (M : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) : Set K) = (fun y : 𝓞 K => c * (y : K)) '' (M : Set (𝓞 K)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«coe_spanSingleton_mul_coeIdeal» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_coe_spanSingleton_mul_coeIdeal_96ae3ce57e4c
