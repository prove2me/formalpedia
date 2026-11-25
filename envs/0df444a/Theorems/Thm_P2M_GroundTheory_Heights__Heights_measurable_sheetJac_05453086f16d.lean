-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d
-- name    : P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:17.650845+00:00
-- url     : https://prove2.me/theorems/1db85b13-b885-467e-bede-cd25c81f65fc
-- title:
--   P2 M Ground Theory Heights  Heights measurable sheet Jac 05453086f16d: P2 M Ground Theory Heights  Heights measurable sheet Jac 05453086f16d
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable sheet Jac 05453086f16d construction uses the P2 M Ground Theory Heights  Heights measurable sheet Jac 05453086f16d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageArea.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSheetImageArea.lean#L15-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageArea
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
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurable_sheetJac» := P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d
