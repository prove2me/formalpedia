-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gaugeBilinearTerm_eq_neg_double_sum
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:41.933148+00:00
-- url     : https://prove2.me/theorems/d83596ee-074b-4a73-bc08-472cea30697c
-- title:
--   Wick Vanishing: gauge Bilinear Term eq neg double sum
-- statement:
--   The Wick Vanishing construction uses the gauge Bilinear Term eq neg double sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L157-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L157-L163

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
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
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum (h : PS k 2 d) (i j : Fin d) :
    sg1 k h i j = -coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) h := by sorry
