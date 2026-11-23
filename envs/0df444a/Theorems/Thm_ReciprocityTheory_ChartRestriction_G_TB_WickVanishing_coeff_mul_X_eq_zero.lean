-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_mul_X_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_mul_X_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:50.986486+00:00
-- url     : https://prove2.me/theorems/b0ed10d3-532b-4e9f-b7e3-fb728fac0b15
-- title:
--   Wick Vanishing: coeff mul X eq zero
-- statement:
--   The Wick Vanishing construction uses the coeff mul X eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HStable.lean#L52-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_mul_X_eq_zero {σ R : Type*} [CommRing R] (p : MvPowerSeries σ R) (s : σ) (n : σ →₀ ℕ) (hn : n s = 0) :
    coeff n (p * X s) = 0 := by sorry
