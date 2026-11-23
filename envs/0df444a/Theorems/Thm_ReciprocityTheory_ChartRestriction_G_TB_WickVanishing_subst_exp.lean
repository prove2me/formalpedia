-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:02.274802+00:00
-- url     : https://prove2.me/theorems/4a02dbcf-efa3-44f5-a02e-d7405b96454c
-- title:
--   Wick Vanishing: subst exp
-- statement:
--   The Wick Vanishing construction uses the subst exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L310-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean#L310-L315

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

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp {k : Type} [CommRing k] [Algebra ℚ k] {σ τ : Type} [Finite σ] (φ : σ → MvPowerSeries τ k)
    (hφ : ∀ s, constantCoeff (φ s) = 0) {a : MvPowerSeries σ k} (ha : constantCoeff a = 0) :
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k) := by sorry
