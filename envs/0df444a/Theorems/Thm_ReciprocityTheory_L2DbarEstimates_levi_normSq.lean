-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_levi_normSq
-- name    : ReciprocityTheory.L2DbarEstimates.levi_normSq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:39.753681+00:00
-- url     : https://prove2.me/theorems/dfc8f131-8bb3-4957-9040-7289665d895f
-- title:
--   L2 Dbar Estimates: levi norm Sq
-- statement:
--   The L2 Dbar Estimates construction uses the levi norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L190-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L190-L213

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

theorem ReciprocityTheory.L2DbarEstimates.levi_normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ‖g y‖ ^ 2) x ξ = ((‖dDot n z g x ξ‖ ^ 2 : ℝ) : ℂ) := by sorry
