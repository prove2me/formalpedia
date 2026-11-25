-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:07.755648+00:00
-- url     : https://prove2.me/theorems/6f917f0c-4d51-4644-9256-a1bf6f86787d
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data abs Norm psi b9d8f94c9e99: P2 M Ground Theory Heights  Theta projective Line Class Data abs Norm psi b9d8f94c9e99
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data abs Norm psi b9d8f94c9e99 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data abs Norm psi b9d8f94c9e99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L251-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L251-L263

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99 (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (Ideal.absNorm ((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) =
      ‖σ (x : K)‖ ^ 2 / ((FractionalIdeal.absNorm (↑ᶠ J) : ℚ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«absNorm_psi» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_absNorm_psi_b9d8f94c9e99
