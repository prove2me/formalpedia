-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_sub_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_sub_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:51.700929+00:00
-- url     : https://prove2.me/theorems/56f55642-c700-5517-ac76-9e0102caf9fc
-- title:
--   C: moll sub eq zero
-- statement:
--   The C construction uses the moll sub eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L22-L30

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
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

theorem ReciprocityTheory.L2DbarEstimates.C.moll_sub_eq_zero {n : ℕ} {t : ℝ} (ht : 0 < t) {x y : V n}
    (hy : y ∉ closedBall x (t / 2)) : moll n t (x - y) = 0 := by sorry
