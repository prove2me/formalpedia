-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_log_one_add
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_log_one_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:22.733852+00:00
-- url     : https://prove2.me/theorems/14e757ef-7e86-53c2-9270-d755a2bf6841
-- title:
--   Wick Vanishing: exp log one add
-- statement:
--   The Wick Vanishing construction uses the exp log one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L273-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L273-L289

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_log_one_add : PowerSeries.subst (PowerSeries.log k) (PowerSeries.exp k) = 1 + PowerSeries.X := by sorry
