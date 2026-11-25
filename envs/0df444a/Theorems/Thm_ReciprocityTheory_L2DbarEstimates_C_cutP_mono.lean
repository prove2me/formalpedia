-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cutP_mono
-- name    : ReciprocityTheory.L2DbarEstimates.C.cutP_mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:53:49.171611+00:00
-- url     : https://prove2.me/theorems/ff3a65bc-a293-5356-831a-98787fe89888
-- title:
--   C: cut P mono
-- statement:
--   The C construction uses the cut P mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L51-L53

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

theorem ReciprocityTheory.L2DbarEstimates.C.cutP_mono {ε s t : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) (hst : s ≤ t) : cutP ε s ≤ cutP ε t := by sorry
