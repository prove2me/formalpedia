-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:48.517205+00:00
-- url     : https://prove2.me/theorems/d1edb33e-12aa-4e9a-be8d-dbb8ff060c83
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data class sum 3b7d7a5b3ec6: P2 M Ground Theory Heights  Theta projective Line Class Data class sum 3b7d7a5b3ec6
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data class sum 3b7d7a5b3ec6 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data class sum 3b7d7a5b3ec6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L322-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L322-L378

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
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6 (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) {s : ℝ}
    (hs : 1 < s) :
    (Units.torsionOrder K : ENNReal) * ∑' t : InvClassIdeals J,
        ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s)) =
      ENNReal.ofReal ((2 / Real.sqrt |(discr K : ℝ)|) ^ s * realEisenstein τ s) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«class_sum» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_class_sum_3b7d7a5b3ec6
