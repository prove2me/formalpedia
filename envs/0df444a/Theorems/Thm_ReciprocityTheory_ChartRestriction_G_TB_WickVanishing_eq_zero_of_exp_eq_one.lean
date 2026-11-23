-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_eq_zero_of_exp_eq_one
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_zero_of_exp_eq_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:06.8112+00:00
-- url     : https://prove2.me/theorems/2c3257a0-a52e-41dc-95fa-a10b913a18b8
-- title:
--   Wick Vanishing: eq zero of exp eq one
-- statement:
--   The Wick Vanishing construction uses the eq zero of exp eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L230-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L230-L234

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.eq_zero_of_exp_eq_one {c : MvPowerSeries σ k} (hc : constantCoeff c = 0)
    (h : PowerSeries.subst c (PowerSeries.exp k) = 1) : c = 0 := by sorry
