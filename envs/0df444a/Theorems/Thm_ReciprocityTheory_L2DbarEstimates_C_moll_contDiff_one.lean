-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff_one
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_contDiff_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:25.995073+00:00
-- url     : https://prove2.me/theorems/f47f8155-2394-41b5-9853-86153c64b13d
-- title:
--   C: moll cont Diff one
-- statement:
--   The C construction uses the moll cont Diff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L20-L20

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

theorem ReciprocityTheory.L2DbarEstimates.C.moll_contDiff_one (n : ℕ) (t : ℝ) : ContDiff ℝ 1 (moll n t) := by sorry
