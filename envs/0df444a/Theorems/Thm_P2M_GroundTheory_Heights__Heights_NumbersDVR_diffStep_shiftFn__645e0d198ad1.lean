-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:14.288793+00:00
-- url     : https://prove2.me/theorems/1f9d1d55-041c-4e21-8fc6-38ea7a857eef
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR diff Step shift Fn  645e0d198ad1: P2 M Ground Theory Heights  Heights Numbers DVR diff Step shift Fn  645e0d198ad1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR diff Step shift Fn  645e0d198ad1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR diff Step shift Fn  645e0d198ad1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1 (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«diffStep_shiftFn'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1
