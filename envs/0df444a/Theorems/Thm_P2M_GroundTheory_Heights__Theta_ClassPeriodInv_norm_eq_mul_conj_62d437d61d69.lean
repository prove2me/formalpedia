-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:37.132964+00:00
-- url     : https://prove2.me/theorems/b10c7c96-60f8-4fc5-b904-0326dfe9e2a7
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv norm eq mul conj 62d437d61d69: P2 M Ground Theory Heights  Theta Class Period Inv norm eq mul conj 62d437d61d69
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv norm eq mul conj 62d437d61d69 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv norm eq mul conj 62d437d61d69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L26-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L26-L43

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
open Classical

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69 (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (x : K) :
    algebraMap ℚ K (Algebra.norm ℚ x) = x * g x := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«norm_eq_mul_conj» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_norm_eq_mul_conj_62d437d61d69
