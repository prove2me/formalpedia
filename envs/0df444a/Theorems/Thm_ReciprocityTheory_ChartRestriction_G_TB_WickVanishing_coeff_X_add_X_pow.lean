-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_X_add_X_pow
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_X_add_X_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:18.308886+00:00
-- url     : https://prove2.me/theorems/55436a84-360b-4d85-9021-8e81b1f727d0
-- title:
--   Wick Vanishing: coeff X add X pow
-- statement:
--   The Wick Vanishing construction uses the coeff X add X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L23-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L23-L48

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_X_add_X_pow (e : Fin 2 →₀ ℕ) (n : ℕ) :
    MvPowerSeries.coeff e (((X 0 : MvPowerSeries (Fin 2) k) + X 1) ^ n) =
      if e 0 + e 1 = n then (n.choose (e 0) : k) else 0 := by sorry
