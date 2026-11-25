-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:56.652868+00:00
-- url     : https://prove2.me/theorems/156ac144-5cc3-5d97-981e-32e1167d82c0
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv int Norm eq mul conj 7233410381a1: P2 M Ground Theory Heights  Theta Class Period Inv int Norm eq mul conj 7233410381a1
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv int Norm eq mul conj 7233410381a1 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv int Norm eq mul conj 7233410381a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L48-L55

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1 (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : 𝓞 K) :
    algebraMap ℤ (𝓞 K) (Algebra.intNorm ℤ (𝓞 K) x) = x * intAut g x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«intNorm_eq_mul_conj» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_intNorm_eq_mul_conj_7233410381a1
