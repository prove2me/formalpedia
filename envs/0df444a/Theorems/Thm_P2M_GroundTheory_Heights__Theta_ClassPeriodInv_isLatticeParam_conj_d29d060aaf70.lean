-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:29.530406+00:00
-- url     : https://prove2.me/theorems/f8263efb-3117-4d71-b4ea-d56b4fc4a508
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param conj d29d060aaf70: P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param conj d29d060aaf70
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param conj d29d060aaf70 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param conj d29d060aaf70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L174-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L174-L183

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70 {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) {w : ℂ} (hw : w ≠ 0) :
    IsLatticeParam ((fun z => w * z) '' (starRingEnd ℂ '' Λ)) (negConj τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«isLatticeParam_conj» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70
