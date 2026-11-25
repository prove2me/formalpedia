-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_abs_second_variation_le
-- name    : ReciprocityTheory.L2DbarEstimates.C.abs_second_variation_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:21.662335+00:00
-- url     : https://prove2.me/theorems/47c04793-a03b-452b-b6cb-eced3518bc8e
-- title:
--   C: abs second variation le
-- statement:
--   The C construction uses the abs second variation le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L104-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutB.lean#L104-L119

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

theorem ReciprocityTheory.L2DbarEstimates.C.abs_second_variation_le {p1 p2 x y z c1 c2 X Y Z : ℝ} (h1 : |p1| ≤ c1) (h2 : |p2| ≤ c2) (hx : |x| ≤ X)
    (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |p2 * (2 * x) * (2 * x) + p1 * (2 * (y + z))| ≤ c2 * (2 * X) * (2 * X) + c1 * (2 * (Y + Z)) := by sorry
