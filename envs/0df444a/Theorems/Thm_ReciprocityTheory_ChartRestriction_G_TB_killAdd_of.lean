-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_killAdd_of
-- name    : ReciprocityTheory.ChartRestriction.G.TB.killAdd_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:30.051132+00:00
-- url     : https://prove2.me/theorems/229c5a29-3ab6-46e9-b1a2-4b99de99af50
-- title:
--   TB: kill Add of
-- statement:
--   The TB construction uses the kill Add of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L51-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L51-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateEqTG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.killAdd_of (hQ : QuadColDerivSt) : KillAddSt := by sorry
