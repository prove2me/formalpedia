-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pushR_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:55:14.014371+00:00
-- url     : https://prove2.me/theorems/c4b5a201-a462-5d04-99c4-be9778128eba
-- title:
--   Chart: push R one
-- statement:
--   The Chart construction uses the push R one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L198-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L198-L212

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
variable {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

theorem ReciprocityTheory.ChartRestriction.G.Chart.pushR_one : pushR G (1 : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) = 1 := by sorry
