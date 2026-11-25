-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_natCast_eq_zero_of_coprime
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:02.002577+00:00
-- url     : https://prove2.me/theorems/67065102-6448-4cef-b25b-f0f1ca05091e
-- title:
--   Power Series Coeff Gaps: nat Cast eq zero of coprime
-- statement:
--   The Power Series Coeff Gaps construction uses the nat Cast eq zero of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L133-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L133-L151

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime {p : ℕ} (hp1 : v (p : K) = 1) {c : ℕ}
    (hc : Nat.Coprime p c) : v (c : K) = 0 := by sorry
