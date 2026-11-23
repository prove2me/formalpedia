-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.db_ofReal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:28.120635+00:00
-- url     : https://prove2.me/theorems/bbdd2320-ed35-4ccc-be29-cadc361a5178
-- title:
--   L2 Dbar Estimates: db of Real
-- statement:
--   The L2 Dbar Estimates construction uses the db of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L305-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L305-L308

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.db_ofReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ) (j : Fin n) (x : M) :
    db n z j (fun y => (ph y : ℂ)) x = (starRingEnd ℂ) (d n z j (fun y => (ph y : ℂ)) x) := by sorry
