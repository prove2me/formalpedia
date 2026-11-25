-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_coeff_single_zero_F_eq_ite
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_single_zero_F_eq_ite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:33.838808+00:00
-- url     : https://prove2.me/theorems/56b5525c-7a05-4088-80e8-b0b35b8ad756
-- title:
--   Nab: coeff single zero F eq ite
-- statement:
--   The Nab construction uses the coeff single zero F eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CoeffActAdd.lean#L11-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FirstDerivativeShiftIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CoeffActAdd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.coeff_single_zero_F_eq_ite {K : Type} [CommRing K] {d : ℕ} (G : FGLaw K d) (c i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by sorry
