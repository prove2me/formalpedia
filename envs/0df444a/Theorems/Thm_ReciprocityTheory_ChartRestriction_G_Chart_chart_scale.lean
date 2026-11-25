-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_chart_scale
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.chart_scale
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:17.241896+00:00
-- url     : https://prove2.me/theorems/91485565-2f0a-5fe1-8eee-f87b7f7ffc47
-- title:
--   Chart: chart scale
-- statement:
--   The Chart construction uses the chart scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanSRestrict.lean#L98-L101

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.chart_scale (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by sorry
