-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_subst_add_two_vars
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:13.781675+00:00
-- url     : https://prove2.me/theorems/432f6ba4-c8c6-458d-91da-e3b28e82ae9d
-- title:
--   Wick Vanishing: exp subst add two vars
-- statement:
--   The Wick Vanishing construction uses the exp subst add two vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L78-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeTrans.lean#L78-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
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
variable (A : Type) [CommRing A] [Algebra ℚ A]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars :
    PowerSeries.subst ((X 0 : MvPowerSeries (Fin 2) A) + X 1) (PowerSeries.exp A) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) *
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) A) (PowerSeries.exp A) := by sorry
