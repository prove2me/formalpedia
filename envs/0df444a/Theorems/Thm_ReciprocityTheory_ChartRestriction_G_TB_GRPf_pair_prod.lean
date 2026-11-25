-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GRPf_pair_prod
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:32.814365+00:00
-- url     : https://prove2.me/theorems/d616c4b0-1220-530b-8133-4935f7100574
-- title:
--   GRPf: pair prod
-- statement:
--   The GRPf construction uses the pair prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeRatio.lean#L25-L34

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
variable {O k : Type} [CommRing O] [StarRing O] [CommRing k] [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.GRPf.pair_prod (c : k) (s s' : O →+* k)
    (h : ∀ a, c * (s a * s (star a) + s' a * s' (star a) - 2 * s a * s' a) = 0) (a : O) :
    c * ((s a - s (star a)) * (s a - s' (star a))) = 0 := by sorry
