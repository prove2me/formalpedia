-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_applyTw
-- name    : ReciprocityTheory.L2DbarEstimates.I.applyTw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:30:31.576885+00:00
-- url     : https://prove2.me/theorems/0fbe9dad-7fd6-4c1f-aeea-d8120e16dc8f
-- title:
--   I: apply Tw
-- statement:
--   The I construction uses the apply Tw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyTw.lean#L11-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyTw.lean#L11-L234

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyTw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.applyTw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hTW : TWStatement n M) (hT : TwistLeviStatement n M) (hD : DualStatement n M)
    (hB : BasicStatement n M) : ApplyStatement n M := by sorry
