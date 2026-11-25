-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_map_ev_one
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.map_ev_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:20.491608+00:00
-- url     : https://prove2.me/theorems/75e3811d-72c7-5b95-ace6-101fdb66b110
-- title:
--   Log Pf: map ev one
-- statement:
--   The Log Pf construction uses the map ev one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogClosed.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogClosed.lean#L91-L93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
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
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by sorry
