-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_foldr_3c1ed327871b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_foldr_3c1ed327871b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:40:07.034866+00:00
-- url     : https://prove2.me/theorems/41de7232-c9d3-4cd9-bce8-9cf9edb9fcb9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq foldr 3c1ed327871b: P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq foldr 3c1ed327871b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq foldr 3c1ed327871b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR v Num L eq foldr 3c1ed327871b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L202-L205

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_foldr_3c1ed327871b (W : Ideal (MRing ι O)) (l : List (K → ℤ)) :
    vNumL W l = eventualValue (l.foldr diffStep (hilbFn (specialIdeal W))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«vNumL_eq_foldr» := P2M_GroundTheory_Heights__Heights_NumbersDVR_vNumL_eq_foldr_3c1ed327871b
