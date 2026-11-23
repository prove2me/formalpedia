-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_hasCompactSupport
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_hasCompactSupport
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:03.367178+00:00
-- url     : https://prove2.me/theorems/622ef59d-62db-4a7b-b299-a7b35ba8a292
-- title:
--   C: moll has Compact Support
-- statement:
--   The C construction uses the moll has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L77-L79

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

theorem ReciprocityTheory.L2DbarEstimates.C.moll_hasCompactSupport (n : ℕ) {t : ℝ} (ht : 0 < t) : HasCompactSupport (moll n t) := by sorry
