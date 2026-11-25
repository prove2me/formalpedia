-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214
-- name    : P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:27.469519+00:00
-- url     : https://prove2.me/theorems/d3b46c9b-5573-43dc-aec4-1332dece6085
-- title:
--   P2 M Ground Theory Heights  Heights lintegral poincare Deep Weight lt top ad8ff22c8214: P2 M Ground Theory Heights  Heights lintegral poincare Deep Weight lt top ad8ff22c8214
-- statement:
--   The P2 M Ground Theory Heights  Heights lintegral poincare Deep Weight lt top ad8ff22c8214 construction uses the P2 M Ground Theory Heights  Heights lintegral poincare Deep Weight lt top ad8ff22c8214 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L60-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepWeightMass.lean#L60-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214 :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lintegral_poincareDeepWeight_lt_top» := P2M_GroundTheory_Heights__Heights_lintegral_poincareDeepWeight_lt_top_ad8ff22c8214
