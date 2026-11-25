-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_le
-- name    : ReciprocityTheory.L2DbarEstimates.I.tl_lw_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:57.709953+00:00
-- url     : https://prove2.me/theorems/d46c89d9-6be7-4896-bd8a-8dc17900b79c
-- title:
--   I: tl lw le
-- statement:
--   The I construction uses the tl lw le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L115-L121

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
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
noncomputable section
open Filter Topology

theorem ReciprocityTheory.L2DbarEstimates.I.tl_lw_le {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r ε : ℝ) (hr : 0 < r)
    (hε : 0 < ε) (hbd : ∀ x, (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) ≤ r ^ 2) (x : M) :
    lw n g ph r ε x ≤ Real.log (1 + ε ^ 2) := by sorry
