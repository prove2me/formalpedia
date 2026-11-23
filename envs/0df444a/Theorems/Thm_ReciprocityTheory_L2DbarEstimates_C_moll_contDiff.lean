-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_contDiff
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_contDiff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:59.750523+00:00
-- url     : https://prove2.me/theorems/4e8719ad-1d98-45df-9008-a4c3ad8db250
-- title:
--   C: moll cont Diff
-- statement:
--   The C construction uses the moll cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/IntegralBumpProfOnePos.lean#L61-L68

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

theorem ReciprocityTheory.L2DbarEstimates.C.moll_contDiff (n : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (moll n t) := by sorry
