-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
-- name    : ReciprocityTheory.L2DbarEstimates.CkR.ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:19.61062+00:00
-- url     : https://prove2.me/theorems/aeaa434a-6fd6-479d-95b4-4c0c760aa712
-- title:
--   Ck R: of Real
-- statement:
--   The Ck R construction uses the of Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L151-L153

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
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

theorem ReciprocityTheory.L2DbarEstimates.CkR.ofReal {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℝ) (hf : CkR n z k f) :
    Ck n z k (fun x => (f x : ℂ)) := by sorry
