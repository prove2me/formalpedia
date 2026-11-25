-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_intCast_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:28.158117+00:00
-- url     : https://prove2.me/theorems/00be9ce3-9a63-4bec-b0af-f5e06cff297c
-- title:
--   Power Series Coeff Gaps: int Cast nonneg
-- statement:
--   The Power Series Coeff Gaps construction uses the int Cast nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L128-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg (n : ℤ) : 0 ≤ v (n : K) := by sorry
