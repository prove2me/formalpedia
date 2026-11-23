-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_finset_sum
-- name    : ReciprocityTheory.L2DbarEstimates.db_finset_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:41.004532+00:00
-- url     : https://prove2.me/theorems/e2b9904e-285a-4e7b-b6ec-7af3fb14d6e5
-- title:
--   L2 Dbar Estimates: db finset sum
-- statement:
--   The L2 Dbar Estimates construction uses the db finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L163-L174

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
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
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.db_finset_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) (j : Fin n) (x : M) :
    db n z j (fun y => ∑ i ∈ s, F i y) x = ∑ i ∈ s, db n z j (F i) x := by sorry
