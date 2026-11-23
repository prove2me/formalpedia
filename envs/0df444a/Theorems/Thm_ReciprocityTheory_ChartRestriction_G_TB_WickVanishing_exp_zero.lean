-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:30.281814+00:00
-- url     : https://prove2.me/theorems/7ac02f1c-0c55-4ef2-8194-ede200158059
-- title:
--   Wick Vanishing: exp zero
-- statement:
--   The Wick Vanishing construction uses the exp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L158-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L158-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero : PowerSeries.subst (0 : MvPowerSeries σ k) (PowerSeries.exp k) = 1 := by sorry
