-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_hasDerivAt_chi
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_hasDerivAt_chi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:47.063722+00:00
-- url     : https://prove2.me/theorems/d7957b72-436c-42cb-876c-d68b31bc2025
-- title:
--   I: ap has Deriv At chi
-- statement:
--   The I construction uses the ap has Deriv At chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L76-L81

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
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
open scoped ENNReal ContDiff Classical

theorem ReciprocityTheory.L2DbarEstimates.I.ap_hasDerivAt_chi (χ : ℝ → ℝ) (hχs : ContDiff ℝ ∞ χ) (ε t : ℝ) :
    HasDerivAt (fun t => χ (t / ε ^ 2)) (deriv χ (t / ε ^ 2) * (1 / ε ^ 2)) t := by sorry
