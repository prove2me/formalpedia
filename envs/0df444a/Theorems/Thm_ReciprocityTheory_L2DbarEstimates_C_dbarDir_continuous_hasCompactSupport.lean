-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_dbarDir_continuous_hasCompactSupport
-- name    : ReciprocityTheory.L2DbarEstimates.C.dbarDir_continuous_hasCompactSupport
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:05.013352+00:00
-- url     : https://prove2.me/theorems/e039093f-5a53-5fe3-80f0-f435da8c8daf
-- title:
--   C: dbar Dir continuous has Compact Support
-- statement:
--   The C construction uses the dbar Dir continuous has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtWeak.lean#L13-L22

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

theorem ReciprocityTheory.L2DbarEstimates.C.dbarDir_continuous_hasCompactSupport {g : V n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (v : V n) :
    Continuous (fun z => dbarDir g z v) ∧ HasCompactSupport (fun z => dbarDir g z v) := by sorry
