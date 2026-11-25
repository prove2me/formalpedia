-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_scale_exp
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GRPf.scale_exp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:25.177817+00:00
-- url     : https://prove2.me/theorems/a4f856a1-0ec5-5ccf-872d-286bf510f844
-- title:
--   GRPf: scale exp
-- statement:
--   The GRPf construction uses the scale exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L115-L120

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

theorem ReciprocityTheory.ChartRestriction.G.TB.GRPf.scale_exp (a : O) {f : MvPowerSeries (GLet T rk) k} (hf : constantCoeff f = 0) :
    scaleBy χ a (PowerSeries.subst f (PowerSeries.exp k)) = PowerSeries.subst (scaleBy χ a f) (PowerSeries.exp k) := by sorry
