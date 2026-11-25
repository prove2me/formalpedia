-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_hypotheses_inhabited_cdb5cef295b2
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_hypotheses_inhabited_cdb5cef295b2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:50.573405+00:00
-- url     : https://prove2.me/theorems/4bea816b-178e-484d-b67e-04dca76c5980
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Norm Identity hypotheses inhabited cdb5cef295b2: P2 M Ground Theory Heights  Heights Vertical Norm Identity hypotheses inhabited cdb5cef295b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Norm Identity hypotheses inhabited cdb5cef295b2 construction uses the P2 M Ground Theory Heights  Heights Vertical Norm Identity hypotheses inhabited cdb5cef295b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/Inhabitants.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/Inhabitants.lean#L72-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormSwap_hypotheses_inhabited_286c010aa601
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightLowerBound_hypotheses_inhabited_32f5e648d58c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightMul_hypotheses_inhabited_0cc03fe7f1d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerMul_hypotheses_inhabited_95e2ae5d82a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MahlerSection_hypotheses_inhabited_066629c10381
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMeanLinear_hypotheses_inhabited_1fdf021d66be

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_hypotheses_inhabited_cdb5cef295b2 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (pointForm.map (algebraMap (𝓞 ℚ) ℚ)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ∃ m, pointForm.coeff m ∉ v.asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«NormIdentity».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Vertical_NormIdentity_hypotheses_inhabited_cdb5cef295b2
