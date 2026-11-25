-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_T_mul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.T_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:37.785621+00:00
-- url     : https://prove2.me/theorems/5b90965b-2b76-5edb-b586-40bc2b41876d
-- title:
--   G2: T mul
-- statement:
--   The G2 construction uses the T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofListSum.lean#L67-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.T_mul (w : List ι) (A B : PS k 1 d) :
    T F u w (A * B) = ((splits w).map (fun p => T F u p.1 A * T F u p.2 B)).sum := by sorry
