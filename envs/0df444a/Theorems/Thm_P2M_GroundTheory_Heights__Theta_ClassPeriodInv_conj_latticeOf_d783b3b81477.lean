-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:34.781456+00:00
-- url     : https://prove2.me/theorems/2e98c413-17fe-4dda-87a8-a2c79ad1ae1b
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv conj lattice Of d783b3b81477: P2 M Ground Theory Heights  Theta Class Period Inv conj lattice Of d783b3b81477
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv conj lattice Of d783b3b81477 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv conj lattice Of d783b3b81477 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L159-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L159-L172

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477 (z : ℂ) :
    starRingEnd ℂ '' latticeOf z = latticeOf (-(starRingEnd ℂ z)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«conj_latticeOf» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477
