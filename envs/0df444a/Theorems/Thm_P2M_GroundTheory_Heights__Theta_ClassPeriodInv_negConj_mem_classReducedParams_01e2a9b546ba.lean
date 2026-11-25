-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:57.785463+00:00
-- url     : https://prove2.me/theorems/dca68ce9-8b82-4184-837c-8895af78957e
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem class Reduced Params 01e2a9b546ba: P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem class Reduced Params 01e2a9b546ba
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem class Reduced Params 01e2a9b546ba construction uses the P2 M Ground Theory Heights  Theta Class Period Inv neg Conj mem class Reduced Params 01e2a9b546ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L195-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L195-L202

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba (hK : finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (A : ClassGroup (𝓞 K)) {τ : ℍ}
    (hτ : τ ∈ classReducedParams σ A) : negConj τ ∈ classReducedParams σ A⁻¹ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«negConj_mem_classReducedParams» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba
