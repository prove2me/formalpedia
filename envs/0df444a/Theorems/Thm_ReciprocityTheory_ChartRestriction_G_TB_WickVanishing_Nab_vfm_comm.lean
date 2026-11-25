-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_vfm_comm
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.vfm_comm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:45.264843+00:00
-- url     : https://prove2.me/theorems/13de295b-40f6-4a4f-a98c-8c32d854bafb
-- title:
--   Nab: vfm comm
-- statement:
--   The Nab construction uses the vfm comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean#L50-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
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
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.vfm_comm (c c' : τ → MvPowerSeries τ k) (f f' G : MvPowerSeries τ k) :
    (vf c (vf c' G - f' * G) - f * (vf c' G - f' * G)) - (vf c' (vf c G - f * G) - f' * (vf c G - f * G)) =
      vf (fun t => vf c (c' t) - vf c' (c t)) G - (vf c f' - vf c' f) * G := by sorry
