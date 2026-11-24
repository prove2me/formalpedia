-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:45.001+00:00
-- url     : https://prove2.me/theorems/3ba415b8-4819-4dca-a1ce-f09f93ddf4f6
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR tendsto sub const at Top 339981f8f00f: P2 M Ground Theory Heights  Heights Numbers DVR tendsto sub const at Top 339981f8f00f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR tendsto sub const at Top 339981f8f00f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR tendsto sub const at Top 339981f8f00f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDegLTClosure.lean#L11-L14

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«tendsto_sub_const_atTop» := P2M_GroundTheory_Heights__Heights_NumbersDVR_tendsto_sub_const_atTop_339981f8f00f
