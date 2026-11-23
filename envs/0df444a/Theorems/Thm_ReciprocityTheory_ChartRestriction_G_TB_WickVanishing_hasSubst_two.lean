-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_two
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.hasSubst_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:55.61969+00:00
-- url     : https://prove2.me/theorems/2c84d80a-874f-4123-96c6-63f3da15614e
-- title:
--   Wick Vanishing: has Subst two
-- statement:
--   The Wick Vanishing construction uses the has Subst two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L107-L108

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.hasSubst_two {a b : MvPowerSeries σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ k) := by sorry
