-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smoothR_ev
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_smoothR_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:22.18172+00:00
-- url     : https://prove2.me/theorems/6659c21a-5ed1-49b9-9d3c-abe2b17c01bb
-- title:
--   I: ap smooth R ev
-- statement:
--   The I construction uses the ap smooth R ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyA.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyA.lean#L70-L80

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_smoothR_ev {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ) (hph : SmoothR n z ph) (r : ℝ) :
    SmoothR n z (ev n g ph r) := by sorry
