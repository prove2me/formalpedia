-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:50.434911+00:00
-- url     : https://prove2.me/theorems/5545b878-ced8-4384-9030-31a0978770ed
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR aeval weighted Homogeneous Component of forms 5c48238267f9: P2 M Ground Theory Heights  Heights Numbers DVR aeval weighted Homogeneous Component of form
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR aeval weighted Homogeneous Component of forms 5c48238267f9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR aeval weighted Homogeneous Component of forms 5c48238267f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L54-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
variable {σ : Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9 {K : Type*} [DecidableEq K] {ι : K → Type*}
    (ω : σ → K → ℕ) (e : σ → MRing ι R) (he : ∀ v, IsMultiHomog (e v) (ω v)) (m : K → ℕ)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent ω m p) =
      weightedHomogeneousComponent (blockWeight ι) m (aeval e p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«aeval_weightedHomogeneousComponent_of_forms» := P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9
