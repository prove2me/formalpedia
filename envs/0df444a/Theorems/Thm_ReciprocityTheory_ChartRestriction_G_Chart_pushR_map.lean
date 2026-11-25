-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_map
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pushR_map
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:05:49.785237+00:00
-- url     : https://prove2.me/theorems/25e9cd73-d0fc-56a8-9834-3369f37d2aa1
-- title:
--   Chart: push R map
-- statement:
--   The Chart construction uses the push R map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RankPf.lean#L179-L186

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory

theorem ReciprocityTheory.ChartRestriction.G.Chart.pushR_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) (e : G ⟶ G) :
    pushR G (y ≫ (Over.pullback (fB R R')).map e) = pushR G y ≫ e := by sorry
