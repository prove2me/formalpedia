-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_fin_two_finsupp_eq_iff
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.fin_two_finsupp_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:58.527716+00:00
-- url     : https://prove2.me/theorems/ae793a3e-08b7-4482-b33c-daf7480aba20
-- title:
--   Wick Vanishing: fin two finsupp eq iff
-- statement:
--   The Wick Vanishing construction uses the fin two finsupp eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L15-L21

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.fin_two_finsupp_eq_iff (e : Fin 2 →₀ ℕ) (m l : ℕ) :
    e = Finsupp.single 0 m + Finsupp.single 1 l ↔ e 0 = m ∧ e 1 = l := by sorry
