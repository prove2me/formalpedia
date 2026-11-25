-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_lift_id_one
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.lift_id_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:58.488486+00:00
-- url     : https://prove2.me/theorems/5a2f8405-c8c5-526b-98e1-b38cbaa63d2e
-- title:
--   Pullback Comparison: lift id one
-- statement:
--   The Pullback Comparison construction uses the lift id one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L108-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L108-L121

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StSiegPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.lift_id_one :
    (lift (𝟙 _) (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G)).left ≫ pφ₂ f G =
      pφ f G ≫ (lift (𝟙 G) (1 : G ⟶ G)).left := by sorry
