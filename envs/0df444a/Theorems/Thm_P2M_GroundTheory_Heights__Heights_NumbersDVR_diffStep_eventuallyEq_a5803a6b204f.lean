-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:26.72886+00:00
-- url     : https://prove2.me/theorems/c1465769-a3dc-4890-bfb3-7817604970fc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR diff Step eventually Eq a5803a6b204f: P2 M Ground Theory Heights  Heights Numbers DVR diff Step eventually Eq a5803a6b204f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR diff Step eventually Eq a5803a6b204f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR diff Step eventually Eq a5803a6b204f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTClosure
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
noncomputable section
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«diffStep_eventuallyEq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_eventuallyEq_a5803a6b204f
