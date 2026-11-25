-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_prod
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pushR_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:24:26.283557+00:00
-- url     : https://prove2.me/theorems/bd5fd665-e7ea-5b88-8460-5dc029858571
-- title:
--   Chart: push R prod
-- statement:
--   The Chart construction uses the push R prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L55-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsAwayNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

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
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]

theorem ReciprocityTheory.ChartRestriction.G.Chart.pushR_prod {d : ℕ} (v : Fin d → (sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G)) :
    pushR G (List.ofFn v).prod = (List.ofFn fun i => pushR G (v i)).prod := by sorry
