-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add
-- name    : ReciprocityTheory.L2DbarEstimates.d_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:25.424513+00:00
-- url     : https://prove2.me/theorems/d78f464e-6eb8-403e-bc84-f058f5770959
-- title:
--   L2 Dbar Estimates: d add
-- statement:
--   The L2 Dbar Estimates construction uses the d add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L229-L235

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

theorem ReciprocityTheory.L2DbarEstimates.d_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y + g y) x = d n z j f x + d n z j g x := by sorry
