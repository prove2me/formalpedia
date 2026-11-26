-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_factorization_factorial_self
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.factorization_factorial_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:34.378805+00:00
-- url     : https://prove2.me/theorems/89f6c978-619d-4914-aaac-1c2dc5d880b9
-- title:
--   Power Series Coeff Gaps: factorization factorial self
-- statement:
--   The Power Series Coeff Gaps construction uses the factorization factorial self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L170-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L170-L178

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.factorization_factorial_self {p : ℕ} (hp : p.Prime) :
    p.factorial.factorization p = 1 := by sorry
