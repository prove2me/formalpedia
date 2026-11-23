-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.d_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:09.453705+00:00
-- url     : https://prove2.me/theorems/2610f950-0656-4426-be2e-b91bd977e37a
-- title:
--   L2 Dbar Estimates: d const mul
-- statement:
--   The L2 Dbar Estimates construction uses the d const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L245-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L245-L251

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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

theorem ReciprocityTheory.L2DbarEstimates.d_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℂ) (f : M → ℂ) (hf : Ck n z 1 f) (j : Fin n) (x : M) :
    d n z j (fun y => c * f y) x = c * d n z j f x := by sorry
