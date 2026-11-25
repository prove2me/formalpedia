-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e
-- name    : P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:51:28.037504+00:00
-- url     : https://prove2.me/theorems/443b7d7f-d025-41ef-b369-02f6baea3c10
-- title:
--   P2 M Ground Theory Heights  Theta Class Period Inv exists eq mul of mk eq 4ce545dc440e: P2 M Ground Theory Heights  Theta Class Period Inv exists eq mul of mk eq 4ce545dc440e
-- statement:
--   The P2 M Ground Theory Heights  Theta Class Period Inv exists eq mul of mk eq 4ce545dc440e construction uses the P2 M Ground Theory Heights  Theta Class Period Inv exists eq mul of mk eq 4ce545dc440e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L204-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassPeriodInvConj.lean#L204-L231

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

theorem P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e {J J' : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K J' = ClassGroup.mk K J) :
    ∃ x : K, x ≠ 0 ∧ ((J' : FractionalIdeal (𝓞 K)⁰ K) : Set K) =
      (fun y => x * y) '' ((J : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ClassPeriodInv».«exists_eq_mul_of_mk_eq» := P2M_GroundTheory_Heights__Theta_ClassPeriodInv_exists_eq_mul_of_mk_eq_4ce545dc440e
