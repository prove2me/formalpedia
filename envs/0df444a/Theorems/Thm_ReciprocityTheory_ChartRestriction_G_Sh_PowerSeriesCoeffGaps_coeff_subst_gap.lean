-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_coeff_subst_gap
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_subst_gap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:17.615824+00:00
-- url     : https://prove2.me/theorems/68573864-68b3-5426-b4af-aa2ed0ede135
-- title:
--   Power Series Coeff Gaps: coeff subst gap
-- statement:
--   The Power Series Coeff Gaps construction uses the coeff subst gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PeriodValuation.lean#L45-L69

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_subst_gap (lg P : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (b : K)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1) (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → coeff j P = 0) :
    coeff M (subst P lg) = coeff M P + coeff M lg * b ^ M := by sorry
