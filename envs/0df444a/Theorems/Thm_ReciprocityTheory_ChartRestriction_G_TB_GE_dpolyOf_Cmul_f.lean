-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_Cmul_f
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_Cmul_f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:37.676471+00:00
-- url     : https://prove2.me/theorems/92a64641-f5b5-4561-bbf9-cf7a39402710
-- title:
--   GE: dpoly Of Cmul f
-- statement:
--   The GE construction uses the dpoly Of Cmul f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L129-L134

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

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_Cmul_f (P : MvPolynomial ι k) (r : k) (f : PS k 1 d) :
    DpolyOf F u P (C r * f) = C r * DpolyOf F u P f := by sorry
