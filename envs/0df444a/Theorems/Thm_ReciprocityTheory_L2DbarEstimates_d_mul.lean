-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul
-- name    : ReciprocityTheory.L2DbarEstimates.d_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:56.252208+00:00
-- url     : https://prove2.me/theorems/d6cb91e5-90c3-4f51-8b26-dd8e26fde586
-- title:
--   L2 Dbar Estimates: d mul
-- statement:
--   The L2 Dbar Estimates construction uses the d mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L261-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L261-L269

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

theorem ReciprocityTheory.L2DbarEstimates.d_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y * g y) x = d n z j f x * g x + f x * d n z j g x := by sorry
