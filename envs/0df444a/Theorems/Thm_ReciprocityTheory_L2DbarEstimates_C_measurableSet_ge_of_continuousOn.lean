-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_measurableSet_ge_of_continuousOn
-- name    : ReciprocityTheory.L2DbarEstimates.C.measurableSet_ge_of_continuousOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:18.591661+00:00
-- url     : https://prove2.me/theorems/3480f5a7-a1b2-4e59-8e24-cddbc2feae0b
-- title:
--   C: measurable Set ge of continuous On
-- statement:
--   The C construction uses the measurable Set ge of continuous On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L39-L48

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.measurableSet_ge_of_continuousOn {W : Set (V n)} (hW : IsOpen W) {f : V n → ℝ}
    (hf : ContinuousOn f W) (c : ℝ) : MeasurableSet {z | z ∈ W ∧ c ≤ f z} := by sorry
