-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_wd_wdb
-- name    : ReciprocityTheory.L2DbarEstimates.comm_wd_wdb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:09:43.341996+00:00
-- url     : https://prove2.me/theorems/ee6f5d42-9c8e-4646-9db3-9a9043f181df
-- title:
--   L2 Dbar Estimates: comm wd wdb
-- statement:
--   The L2 Dbar Estimates construction uses the comm wd wdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L51-L62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
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

theorem ReciprocityTheory.L2DbarEstimates.comm_wd_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wd n j (wdb n k g) y = wdb n k (wd n j g) y := by sorry
