-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_comp_real
-- name    : ReciprocityTheory.L2DbarEstimates.d_comp_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:50.579796+00:00
-- url     : https://prove2.me/theorems/fad2c81e-7e96-4e19-b0ed-73d033f949c7
-- title:
--   L2 Dbar Estimates: d comp real
-- statement:
--   The L2 Dbar Estimates construction uses the d comp real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L330-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L330-L341

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

theorem ReciprocityTheory.L2DbarEstimates.d_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (ph : M → ℝ) (hph : CkR n z 1 ph) (j : Fin n) (x : M) :
    d n z j (fun y => (k (ph y) : ℂ)) x = ((deriv k (ph x) : ℝ) : ℂ) * d n z j (fun y => (ph y : ℂ)) x := by sorry
