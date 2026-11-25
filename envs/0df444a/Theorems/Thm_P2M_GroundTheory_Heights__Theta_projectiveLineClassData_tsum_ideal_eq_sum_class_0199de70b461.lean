-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:51.469546+00:00
-- url     : https://prove2.me/theorems/75be3792-edbc-4a91-83d4-4b7187673973
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data tsum ideal eq sum class 0199de70b461: P2 M Ground Theory Heights  Theta projective Line Class Data tsum ideal eq sum class 0199de70b461
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data tsum ideal eq sum class 0199de70b461 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data tsum ideal eq sum class 0199de70b461 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L67-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
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
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461 {s : ℝ} (hs : 0 < s) :
    ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) =
      ∑ B : ClassGroup (𝓞 K), ∑' I : (ClassGroup.mk0 ⁻¹' {B} : Set (Ideal (𝓞 K))⁰),
        ENNReal.ofReal ((Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«tsum_ideal_eq_sum_class» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_ideal_eq_sum_class_0199de70b461
