-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:51:23.832814+00:00
-- url     : https://prove2.me/theorems/412a926e-5abd-4a11-94ec-bf774797fe2a
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv mul map eq span abs Norm 19aa514c4350: P2 M Ground Theory Heights  Theta Class Period Inv mul map eq span abs Norm 19aa514c4350
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv mul map eq span abs Norm 19aa514c4350 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv mul map eq span abs Norm 19aa514c4350 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L66-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L66-L91

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350 (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (g : K ≃ₐ[ℚ] K) (hg : ∀ x, σ (g x) = starRingEnd ℂ (σ x)) (I : Ideal (𝓞 K)) :
    I * I.map (intAut g) = Ideal.span {((Ideal.absNorm I : ℤ) : 𝓞 K)} := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«mul_map_eq_span_absNorm» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_mul_map_eq_span_absNorm_19aa514c4350
