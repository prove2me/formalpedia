-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_ChPt_eq_of_mod
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.eq_of_mod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:05.484256+00:00
-- url     : https://prove2.me/theorems/02f902eb-3107-4a68-907f-f629d3816010
-- title:
--   Ch Pt: eq of mod
-- statement:
--   The Ch Pt construction uses the eq of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/ChartPointCongruence/EqOfMod.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/ChartPointCongruence/EqOfMod.lean#L86-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext

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
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.eq_of_mod {O : Type} [CommRing O] (p : O) (hH : IsHausdorff (Ideal.span {p}) O) (u w : O)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w) : u = w := by sorry
