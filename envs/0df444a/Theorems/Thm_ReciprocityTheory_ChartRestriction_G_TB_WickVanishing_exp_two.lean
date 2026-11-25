-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_two
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_two
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:35.689275+00:00
-- url     : https://prove2.me/theorems/0f9ba34d-5609-43b0-a292-834eb08dbc75
-- title:
--   Wick Vanishing: exp two
-- statement:
--   The Wick Vanishing construction uses the exp two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L50-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L50-L99

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
variable (k : Type) [CommRing k] [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_two :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) k) + X 1) (PowerSeries.exp k) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by sorry
