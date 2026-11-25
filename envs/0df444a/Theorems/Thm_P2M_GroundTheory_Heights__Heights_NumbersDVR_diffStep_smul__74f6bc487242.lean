-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:32.754876+00:00
-- url     : https://prove2.me/theorems/436e63c2-1479-47ef-8c01-8407cda832c2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR diff Step smul  74f6bc487242: P2 M Ground Theory Heights  Heights Numbers DVR diff Step smul  74f6bc487242
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR diff Step smul  74f6bc487242 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR diff Step smul  74f6bc487242 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L15-L17

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242 (b : K → ℤ) (c : ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (c • f) = c • diffStep b f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«diffStep_smul'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_smul__74f6bc487242
