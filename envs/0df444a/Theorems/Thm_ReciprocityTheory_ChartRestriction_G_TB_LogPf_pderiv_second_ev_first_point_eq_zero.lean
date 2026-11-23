-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_second_ev_first_point_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_second_ev_first_point_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:47.31372+00:00
-- url     : https://prove2.me/theorems/7c3221d5-77ac-4ab4-867d-88ff2c58e9b2
-- title:
--   Log Pf: pderiv second ev first point eq zero
-- statement:
--   The Log Pf construction uses the pderiv second ev first point eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/PderivSecondEvFirstPointEqZero.lean#L131-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/PderivSecondEvFirstPointEqZero.lean#L131-L158

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

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_second_ev_first_point_eq_zero (h : PS k 1 d) (b : Fin d) : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] h) = 0 := by sorry
