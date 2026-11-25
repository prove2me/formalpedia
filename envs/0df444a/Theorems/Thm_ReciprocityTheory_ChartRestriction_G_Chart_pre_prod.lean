-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pre_prod
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pre_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:37.931508+00:00
-- url     : https://prove2.me/theorems/9189b87d-c64e-5f46-8036-e9942e4c2883
-- title:
--   Chart: pre prod
-- statement:
--   The Chart construction uses the pre prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullbackFactor.lean#L22-L26

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
variable {R : Type} [CommRing R] {M : Over (Spec (CommRingCat.of R))} [GrpObj M]

theorem ReciprocityTheory.ChartRestriction.G.Chart.pre_prod {X Y : Over (Spec (CommRingCat.of R))} (f : Y ⟶ X) {d : ℕ} (v : Fin d → (X ⟶ M)) :
    f ≫ (List.ofFn v).prod = (List.ofFn fun i => f ≫ v i).prod := by sorry
