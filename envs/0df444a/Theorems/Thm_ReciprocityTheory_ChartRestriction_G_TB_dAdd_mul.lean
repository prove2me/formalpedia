-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_dAdd_mul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.dAdd_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:27.295449+00:00
-- url     : https://prove2.me/theorems/8fa2b69a-93c2-51f3-9c10-685265044b6a
-- title:
--   TB: d Add mul
-- statement:
--   The TB construction uses the d Add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/KillAdd.lean#L43-L49

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

theorem ReciprocityTheory.ChartRestriction.G.TB.dAdd_mul (u : Fin d → k) (b : Fin n) (f g : PS k n d) :
    dAdd u b (f * g) = dAdd u b f * g + f * dAdd u b g := by sorry
