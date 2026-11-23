-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_sum_P
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_sum_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:10.140515+00:00
-- url     : https://prove2.me/theorems/62dedeb5-b9d6-4b5a-9c7d-6c831aca7545
-- title:
--   GE: dpoly Of sum P
-- statement:
--   The GE construction uses the dpoly Of sum P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L113-L120

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

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_sum_P {α : Type} (s : Finset α) (P : α → MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (∑ a ∈ s, P a) f = ∑ a ∈ s, DpolyOf F u (P a) f := by sorry
