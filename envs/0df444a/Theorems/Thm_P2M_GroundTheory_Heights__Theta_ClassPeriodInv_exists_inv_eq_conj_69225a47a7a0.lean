-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:38.092041+00:00
-- url     : https://prove2.me/theorems/5a4d4ec9-ef74-4051-98e6-aaf93accf65d
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv exists inv eq conj 69225a47a7a0: P2 M Ground Theory Heights  Theta Class Period Inv exists inv eq conj 69225a47a7a0
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv exists inv eq conj 69225a47a7a0 construction uses the P2 M Ground Theory Heights  Theta Class Period Inv exists inv eq conj 69225a47a7a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L105-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L105-L157

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0 (hK : finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ w : ℂ, w ≠ 0 ∧ σ '' (((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Set K) = (fun z => w * z) '' (starRingEnd ℂ '' (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) :
        Set K))) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«exists_inv_eq_conj» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_inv_eq_conj_69225a47a7a0
