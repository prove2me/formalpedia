-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_d2
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.d2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:10.823688+00:00
-- url     : https://prove2.me/theorems/4baec827-ff02-42b6-8b78-a3968640992c
-- title:
--   Nab: d2
-- statement:
--   The Nab construction uses the d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyFirstZeroSecond.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/IntegralFamilyFirstZeroSecond.lean#L15-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
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
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.d2 {n : ℕ} {p q : Pt k n d} (hpq : CZ (![p, q] : Fin 2 → Pt k n d)) (h : PS k 2 d) (v : Fin n × Fin d) :
    pderiv k v (ev (n := n) ![p, q] h) = ∑ c, ev (n := n) ![p, q] (pderiv k ((0 : Fin 2), c) h) * pderiv k v (p c) +
      ∑ c, ev (n := n) ![p, q] (pderiv k ((1 : Fin 2), c) h) * pderiv k v (q c) := by sorry
