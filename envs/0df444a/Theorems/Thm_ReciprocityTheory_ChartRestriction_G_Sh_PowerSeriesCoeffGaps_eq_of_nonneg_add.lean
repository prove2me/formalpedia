-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_eq_of_nonneg_add
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.eq_of_nonneg_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:44.208131+00:00
-- url     : https://prove2.me/theorems/5ead72f3-e925-45c2-9ecd-1ad664b5ecf8
-- title:
--   Power Series Coeff Gaps: eq of nonneg add
-- statement:
--   The Power Series Coeff Gaps construction uses the eq of nonneg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L180-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L180-L186

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.eq_of_nonneg_add {x y : K} {A B : ℝ} (hA : A < 0) (hx : v x = A) (hy : v y = B)
    (h : 0 ≤ v (x + y)) : A = B := by sorry
