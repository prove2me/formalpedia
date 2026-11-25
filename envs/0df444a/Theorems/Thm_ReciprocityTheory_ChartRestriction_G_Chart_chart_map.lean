-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_map
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.chart_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:28.723303+00:00
-- url     : https://prove2.me/theorems/ebb1b1fd-ae73-5f01-a777-0413ca9f957f
-- title:
--   Chart: chart map
-- statement:
--   The Chart construction uses the chart map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L91-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ChartAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]

theorem ReciprocityTheory.ChartRestriction.G.Chart.chart_map {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[Localization.Away s] A')
    (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (dualMapS (j.restrictScalars S)) ≫ pushR G (pt C h) = pushR G (pt C ((dualMapS j).comp h)) := by sorry
