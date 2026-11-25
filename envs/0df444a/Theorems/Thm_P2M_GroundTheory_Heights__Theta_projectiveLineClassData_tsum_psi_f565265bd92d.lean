-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:43.547863+00:00
-- url     : https://prove2.me/theorems/279887f1-20ec-4080-bc6d-b9ca3524aa5b
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data tsum psi f565265bd92d: P2 M Ground Theory Heights  Theta projective Line Class Data tsum psi f565265bd92d
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data tsum psi f565265bd92d construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data tsum psi f565265bd92d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L225-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L225-L239

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
open FractionalIdeal
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (g : InvClassIdeals J → ENNReal) :
    ∑' x : Nz J, g (psi J x) = (Units.torsionOrder K : ENNReal) * ∑' t, g t := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«tsum_psi» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_tsum_psi_f565265bd92d
