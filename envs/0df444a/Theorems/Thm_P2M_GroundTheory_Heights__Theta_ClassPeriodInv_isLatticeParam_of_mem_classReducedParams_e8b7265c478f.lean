-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:03.307545+00:00
-- url     : https://prove2.me/theorems/a0c4c78d-3130-56da-86aa-f1d00d86b6dd
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param of mem class Reduced Params e8b7265c478f: P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param of mem class Reduced P
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param of mem class Reduced Params e8b7265c478f construction uses the P2 M Ground Theory Heights  Theta Class Period Inv is Lattice Param of mem class Reduced Params e8b7265c478f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L241-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L241-L254

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f (σ : K →+* ℂ) {A : ClassGroup (𝓞 K)} {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hJ : ClassGroup.mk K J = A) :
    IsLatticeParam (σ '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K)) τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«isLatticeParam_of_mem_classReducedParams» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f
