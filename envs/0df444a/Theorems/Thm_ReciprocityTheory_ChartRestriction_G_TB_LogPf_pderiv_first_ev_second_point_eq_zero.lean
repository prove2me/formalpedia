-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_first_ev_second_point_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_first_ev_second_point_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:12.904881+00:00
-- url     : https://prove2.me/theorems/2d5a76c9-cf6f-45d3-aa8e-36388207a1b4
-- title:
--   Log Pf: pderiv first ev second point eq zero
-- statement:
--   The Log Pf construction uses the pderiv first ev second point eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/PderivSecondEvFirstPointEqZero.lean#L102-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/PderivSecondEvFirstPointEqZero.lean#L102-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_first_ev_second_point_eq_zero (h : PS k 1 d) (a : Fin d) : pderiv k ((0 : Fin 2), a) (ev (n := 2) ![pt k d 1] h) = 0 := by sorry
