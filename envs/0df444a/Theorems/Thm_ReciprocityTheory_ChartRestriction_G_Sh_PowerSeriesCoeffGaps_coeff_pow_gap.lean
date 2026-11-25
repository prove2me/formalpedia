-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_pow_gap
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_pow_gap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:23:31.384899+00:00
-- url     : https://prove2.me/theorems/0def2dc2-f30c-4936-a183-7fe1528c0aea
-- title:
--   Power Series Coeff Gaps: coeff pow gap
-- statement:
--   The Power Series Coeff Gaps construction uses the coeff pow gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L14-L43

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_pow_gap (f : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (a : K)
    (h0 : coeff 0 f = 0) (h1 : coeff 1 f = a) (hg : ∀ j, 2 ≤ j → j < M → coeff j f = 0)
    (n : ℕ) (hn : 2 ≤ n) : coeff M (f ^ n) = if n = M then a ^ M else 0 := by sorry
