-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_dual_dbarDot_comp_real
-- name    : ReciprocityTheory.L2DbarEstimates.I.dual_dbarDot_comp_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:56:50.710629+00:00
-- url     : https://prove2.me/theorems/a0358c52-23c7-4aed-b712-998672b8b918
-- title:
--   I: dual dbar Dot comp real
-- statement:
--   The I construction uses the dual dbar Dot comp real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean#L77-L88

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.dual_dbarDot_comp_real {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ)
    (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : CkR n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    ‖dbarDot n z (fun y => (k (f y) : ℂ)) x ξ‖ =
      |deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by sorry
