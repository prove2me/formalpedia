-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_conj
-- name    : ReciprocityTheory.L2DbarEstimates.d_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:20.547417+00:00
-- url     : https://prove2.me/theorems/94e44a31-dd80-4bc2-bede-f1faf217ed2c
-- title:
--   L2 Dbar Estimates: d conj
-- statement:
--   The L2 Dbar Estimates construction uses the d conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L297-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L297-L303

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

theorem ReciprocityTheory.L2DbarEstimates.d_conj {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (j : Fin n) (x : M) :
    d n z j (fun y => (starRingEnd ℂ) (f y)) x = (starRingEnd ℂ) (db n z j f x) := by sorry
