-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuousOn_cutComp
-- name    : ReciprocityTheory.L2DbarEstimates.C.continuousOn_cutComp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:38.920002+00:00
-- url     : https://prove2.me/theorems/b43e87a4-9a3d-46bb-86ef-639f50f302c7
-- title:
--   C: continuous On cut Comp
-- statement:
--   The C construction uses the continuous On cut Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L93-L97

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutB
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
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.continuousOn_cutComp {T : Set (V n)} {F : V n → ℂ} (hFc : ContinuousOn F T) {g : ℝ → ℝ}
    (hg : ∀ s, 0 ≤ s → ContinuousAt g s) : ContinuousOn (fun z => g (‖F z‖ ^ 2)) T := by sorry
