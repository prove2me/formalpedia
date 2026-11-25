-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:31.802996+00:00
-- url     : https://prove2.me/theorems/5896f9ca-e8b8-4f18-b3f2-952ebbe45698
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param mul 5bec8bc1e470: P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param mul 5bec8bc1e470
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param mul 5bec8bc1e470 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param mul 5bec8bc1e470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L233-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L233-L239

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470 {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) {w : ℂ} (hw : w ≠ 0) :
    IsLatticeParam ((fun z => w * z) '' Λ) τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«isLatticeParam_mul» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470
