-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_coeff_scale
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GRPf.coeff_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:30.641156+00:00
-- url     : https://prove2.me/theorems/26290773-e549-4dad-83c0-b59b1aad7d96
-- title:
--   GRPf: coeff scale
-- statement:
--   The GRPf construction uses the coeff scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L105-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeRatio
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GRPf
variable {O k T : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k] [Fintype T] {rk : T → ℕ}
  (χ : T → O →+* k)

theorem ReciprocityTheory.ChartRestriction.G.TB.GRPf.coeff_scale (a : O) (f : MvPowerSeries (GLet T rk) k) (m : GLet T rk →₀ ℕ) :
    coeff m (scaleBy χ a f) = (m.prod fun l e => χ l.1 a ^ e) * coeff m f := by sorry
