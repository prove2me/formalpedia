-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_secondOrder
-- name    : ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_secondOrder
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:59.733671+00:00
-- url     : https://prove2.me/theorems/a236d4f1-063b-4b60-801a-e47a575e09d8
-- title:
--   GE: deg Lt second Order
-- statement:
--   The GE construction uses the deg Lt second Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L186-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean#L186-L195

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
variable {ι : Type} [Fintype ι]

theorem ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_secondOrder (c : ι → ι → k) {n : ℕ} {P : MvPolynomial ι k} (h : DegLt (n + 1) P) :
    DegLt n (secondOrder k c P) := by sorry
