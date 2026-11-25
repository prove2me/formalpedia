-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_tl_lw_smoothR
-- name    : ReciprocityTheory.L2DbarEstimates.I.tl_lw_smoothR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:02.367992+00:00
-- url     : https://prove2.me/theorems/d5b1e8ab-c549-4d2a-a63c-ab99e65d4a77
-- title:
--   I: tl lw smooth R
-- statement:
--   The I construction uses the tl lw smooth R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L132-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean#L132-L147

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

theorem ReciprocityTheory.L2DbarEstimates.I.tl_lw_smoothR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r δ : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) (hδ : 0 < δ) :
    SmoothR n z (lw n g ph r δ) := by sorry
