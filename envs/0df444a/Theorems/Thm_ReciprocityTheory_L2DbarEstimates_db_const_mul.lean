-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.db_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:15.29799+00:00
-- url     : https://prove2.me/theorems/52f353ee-11f0-4c96-90ae-ce20d6442021
-- title:
--   L2 Dbar Estimates: db const mul
-- statement:
--   The L2 Dbar Estimates construction uses the db const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L253-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L253-L259

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
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

theorem ReciprocityTheory.L2DbarEstimates.db_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    db n z j (fun y => c * f y) x = c * db n z j f x := by sorry
