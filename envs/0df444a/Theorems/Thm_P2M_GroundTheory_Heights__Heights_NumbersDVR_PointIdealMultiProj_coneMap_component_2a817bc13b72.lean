-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_component_2a817bc13b72
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_component_2a817bc13b72
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:35.470163+00:00
-- url     : https://prove2.me/theorems/f87c6b2f-9dfb-4d87-968c-32bad4bf0298
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map component 2a817bc13b72: P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map component 2a817b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map component 2a817bc13b72 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map component 2a817bc13b72 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPointIdealMultiProj.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPointIdealMultiProj.lean#L27-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_component_2a817bc13b72 (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PointIdealMultiProj».«coneMap_component» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_component_2a817bc13b72
