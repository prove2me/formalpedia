-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isAddHaar_regular_1d20c7caa245
-- name    : P2M_GroundTheory_Heights__Theta_isAddHaar_regular_1d20c7caa245
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:46.959549+00:00
-- url     : https://prove2.me/theorems/862aa168-0b99-4414-af23-68fe506108e0
-- title:
--   P2 M Ground Theory Heights  Theta is Add Haar regular 1d20c7caa245: P2 M Ground Theory Heights  Theta is Add Haar regular 1d20c7caa245
-- statement:
--   The P2 M Ground Theory Heights  Theta is Add Haar regular 1d20c7caa245 construction uses the P2 M Ground Theory Heights  Theta is Add Haar regular 1d20c7caa245 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L224-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L224-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise

theorem P2M_GroundTheory_Heights__Theta_isAddHaar_regular_1d20c7caa245 {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.Regular := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isAddHaar_regular» := P2M_GroundTheory_Heights__Theta_isAddHaar_regular_1d20c7caa245
