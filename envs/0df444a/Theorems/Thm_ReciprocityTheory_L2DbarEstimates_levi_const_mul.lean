-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_const_mul
-- name    : ReciprocityTheory.L2DbarEstimates.levi_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:45.483389+00:00
-- url     : https://prove2.me/theorems/7300a28d-5c3a-4506-9872-ca64b6493e54
-- title:
--   L2 Dbar Estimates: levi const mul
-- statement:
--   The L2 Dbar Estimates construction uses the levi const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L175-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L175-L188

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
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

theorem ReciprocityTheory.L2DbarEstimates.levi_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (ph : M → ℝ) (hph : CkR n z 2 ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => c * ph y) x ξ = (c : ℂ) * Levi n z ph x ξ := by sorry
