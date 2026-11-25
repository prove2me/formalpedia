-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_log_exp
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.log_exp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:23.987485+00:00
-- url     : https://prove2.me/theorems/6e2ebb04-90af-4037-a03f-a6674ab4afc2
-- title:
--   Wick Vanishing: log exp
-- statement:
--   The Wick Vanishing construction uses the log exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L303-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L303-L304

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.log_exp {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a := by sorry
