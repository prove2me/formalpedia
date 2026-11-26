-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_eq_zero_of_symm
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_eq_zero_of_symm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:32.513086+00:00
-- url     : https://prove2.me/theorems/caaf5957-e1a7-5904-8dbe-af98512a99fa
-- title:
--   Power Series Coeff Gaps: coeff eq zero of symm
-- statement:
--   The Power Series Coeff Gaps construction uses the coeff eq zero of symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L87-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L87-L106

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_eq_zero_of_symm [IsAlgClosed K] [CharZero K] (lg : PowerSeries K) (M : ℕ)
    (hM : 2 ≤ M) (h : ∀ z : K, z ^ (M - 1) = 1 → rescale z lg = z • lg) (j : ℕ)
    (hj2 : 2 ≤ j) (hj : j < M) : coeff j lg = 0 := by sorry
