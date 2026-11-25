-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_chartSlice_symm_apply
-- name    : ReciprocityTheory.L2DbarEstimates.chartSlice_symm_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:22.829613+00:00
-- url     : https://prove2.me/theorems/484f2d14-c066-4082-9cd1-47aa43e8edf3
-- title:
--   L2 Dbar Estimates: chart Slice symm apply
-- statement:
--   The L2 Dbar Estimates construction uses the chart Slice symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L26-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.chartSlice_symm_apply {M : Type*} [TopologicalSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {p : ℕ} (i : Fin p) (y : V n) :
    (chartSlice e i).symm y = (e.symm y, i) := by sorry
