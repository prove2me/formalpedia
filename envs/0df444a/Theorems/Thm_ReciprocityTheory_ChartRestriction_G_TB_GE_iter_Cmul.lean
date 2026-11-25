-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_iter_Cmul
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.iter_Cmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:25.544728+00:00
-- url     : https://prove2.me/theorems/b5335964-93b9-5a2f-9fc2-2b67fecbfc35
-- title:
--   GE: iter Cmul
-- statement:
--   The GE construction uses the iter Cmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L33-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.iter_Cmul (D : PS k 1 d → PS k 1 d) (hD : ∀ (r : k) f, D (C r * f) = C r * D f) (n : ℕ) (r : k)
    (f : PS k 1 d) : D^[n] (C r * f) = C r * D^[n] f := by sorry
