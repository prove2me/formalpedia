-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_expComp_gap
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_expComp_gap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:32.547373+00:00
-- url     : https://prove2.me/theorems/eac2437a-9b41-5347-9e17-347c904f4375
-- title:
--   Power Series Coeff Gaps: coeff exp Comp gap
-- statement:
--   The Power Series Coeff Gaps construction uses the coeff exp Comp gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L71-L85

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
variable {K : Type*} [Field K]

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_expComp_gap [CharZero K] (Ω : K) (lg : PowerSeries K) (M : ℕ) (hM : 2 ≤ M)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0) :
    coeff M (expComp Ω lg) = Ω * coeff M lg + Ω ^ M / (M.factorial : K) := by sorry
