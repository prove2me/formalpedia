-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_polydiscCutoff_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.C.polydiscCutoff_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:33.395176+00:00
-- url     : https://prove2.me/theorems/64078a67-948b-42bc-a034-001bf7a82b03
-- title:
--   C: polydisc Cutoff nonneg
-- statement:
--   The C construction uses the polydisc Cutoff nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L47-L49

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
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

theorem ReciprocityTheory.L2DbarEstimates.C.polydiscCutoff_nonneg (ε s : ℝ) : 0 ≤ cutP ε s := by sorry
