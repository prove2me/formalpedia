-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_add
-- name    : ReciprocityTheory.L2DbarEstimates.CkR.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:16:03.660983+00:00
-- url     : https://prove2.me/theorems/f4004618-f293-47d3-949e-c649f3841bb0
-- title:
--   Ck R: add
-- statement:
--   The Ck R construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L139-L143

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

theorem ReciprocityTheory.L2DbarEstimates.CkR.add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f g : M → ℝ) (hf : CkR n z k f) (hg : CkR n z k g) :
    CkR n z k (fun x => f x + g x) := by sorry
