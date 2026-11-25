-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tubeWeight_351f13760ff2
-- name    : P2M_GroundTheory_Heights__Heights_measurable_tubeWeight_351f13760ff2
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:56.420695+00:00
-- url     : https://prove2.me/theorems/722172d1-d156-4a17-ac41-66767d15ae31
-- title:
--   P2 M Ground Theory Heights  Heights measurable tube Weight 351f13760ff2: P2 M Ground Theory Heights  Heights measurable tube Weight 351f13760ff2
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable tube Weight 351f13760ff2 construction uses the P2 M Ground Theory Heights  Heights measurable tube Weight 351f13760ff2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOffTube.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
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
open MvPolynomial MeasureTheory Filter Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_measurable_tubeWeight_351f13760ff2 {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) : Measurable (tubeWeight Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurable_tubeWeight» := P2M_GroundTheory_Heights__Heights_measurable_tubeWeight_351f13760ff2
