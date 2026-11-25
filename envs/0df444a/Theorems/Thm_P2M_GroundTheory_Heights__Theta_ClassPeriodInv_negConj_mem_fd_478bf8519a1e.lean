-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:38.56146+00:00
-- url     : https://prove2.me/theorems/89a844d4-59ba-482a-8483-9968ee1f31b9
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem fd 478bf8519a1e: P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem fd 478bf8519a1e
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem fd 478bf8519a1e construction uses the P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem fd 478bf8519a1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L185-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L185-L193

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e {τ : ℍ} (h : τ ∈ 𝒟) : negConj τ ∈ 𝒟 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«negConj_mem_fd» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_fd_478bf8519a1e
