-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuousAt_cutP
-- name    : ReciprocityTheory.L2DbarEstimates.C.continuousAt_cutP
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:48.305449+00:00
-- url     : https://prove2.me/theorems/466ec0b5-afa5-5dd7-8aa5-f5ac15f6c207
-- title:
--   C: continuous At cut P
-- statement:
--   The C construction uses the continuous At cut P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L90-L91

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

theorem ReciprocityTheory.L2DbarEstimates.C.continuousAt_cutP {ε s : ℝ} (h : 0 < s + ε) : ContinuousAt (cutP ε) s := by sorry
