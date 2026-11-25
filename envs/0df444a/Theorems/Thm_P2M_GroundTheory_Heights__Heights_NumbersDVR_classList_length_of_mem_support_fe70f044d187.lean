-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_length_of_mem_support_fe70f044d187
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_length_of_mem_support_fe70f044d187
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:27:41.343666+00:00
-- url     : https://prove2.me/theorems/19c273a9-0945-5671-ad9b-258540c630ed
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR class List length of mem support fe70f044d187: P2 M Ground Theory Heights  Heights Numbers DVR class List length of mem support fe70f044d187
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR class List length of mem support fe70f044d187 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR class List length of mem support fe70f044d187 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L241-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L241-L249

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_length_of_mem_support_fe70f044d187 {σ : Type*} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ}
    {t : ℕ} (hH : H.IsHomogeneous t) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«classList_length_of_mem_support» := P2M_GroundTheory_Heights__Heights_NumbersDVR_classList_length_of_mem_support_fe70f044d187
