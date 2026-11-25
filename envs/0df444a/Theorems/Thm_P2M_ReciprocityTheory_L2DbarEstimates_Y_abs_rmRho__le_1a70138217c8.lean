-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8
-- name    : P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:10.842585+00:00
-- url     : https://prove2.me/theorems/0caeafdc-4a4b-4534-ad6a-325958713c8f
-- title:
--   P2 M Reciprocity Theory L2 Dbar Estimates Y abs rm Rho  le 1a70138217c8: P2 M Reciprocity Theory L2 Dbar Estimates Y abs rm Rho  le 1a70138217c8
-- statement:
--   The P2 M Reciprocity Theory L2 Dbar Estimates Y abs rm Rho  le 1a70138217c8 construction uses the P2 M Reciprocity Theory L2 Dbar Estimates Y abs rm Rho  le 1a70138217c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/RegMaxA.lean#L76-L81

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8 (t : ℝ) : |rmRho' t| ≤ 1 := by sorry

alias «ReciprocityTheory».«L2DbarEstimates».«Y».«abs_rmRho'_le» := P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8
