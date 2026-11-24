-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:30.227053+00:00
-- url     : https://prove2.me/theorems/423b2bab-f289-48ec-984b-2e22a982b07a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR diff Step comm  50e9b5a46128: P2 M Ground Theory Heights  Heights Numbers DVR diff Step comm  50e9b5a46128
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR diff Step comm  50e9b5a46128 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR diff Step comm  50e9b5a46128 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMixedDiffLinear.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128 (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«diffStep_comm'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128
