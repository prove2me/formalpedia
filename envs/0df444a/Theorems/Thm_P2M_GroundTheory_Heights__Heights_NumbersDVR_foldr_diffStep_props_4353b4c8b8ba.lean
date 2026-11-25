-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:50.592507+00:00
-- url     : https://prove2.me/theorems/829bd771-1bf9-5675-88f5-b51e69a42cbc
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step props 4353b4c8b8ba: P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step props 4353b4c8b8ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step props 4353b4c8b8ba construction uses the P2 M Ground Theory Heights  Heights Numbers DVR foldr diff Step props 4353b4c8b8ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L27-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
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
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba (l : List (K → ℤ)) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ) :
    l.foldr diffStep (f + g) = l.foldr diffStep f + l.foldr diffStep g ∧
    l.foldr diffStep (c • f) = c • l.foldr diffStep f ∧
    l.foldr diffStep (shiftFn s f) = shiftFn s (l.foldr diffStep f) ∧
    l.foldr diffStep (diffStep b f) = diffStep b (l.foldr diffStep f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«foldr_diffStep_props» := P2M_GroundTheory_Heights__Heights_NumbersDVR_foldr_diffStep_props_4353b4c8b8ba
