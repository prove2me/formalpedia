-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_nonneg
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:55:10.022118+00:00
-- url     : https://prove2.me/theorems/2b6a5d0c-462c-4663-8583-2e83cfd343c7
-- title:
--   C: moll nonneg
-- statement:
--   The C construction uses the moll nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L57-L59

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
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
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.C.moll_nonneg (n : ℕ) (t : ℝ) (z : V n) : 0 ≤ moll n t z := by sorry
