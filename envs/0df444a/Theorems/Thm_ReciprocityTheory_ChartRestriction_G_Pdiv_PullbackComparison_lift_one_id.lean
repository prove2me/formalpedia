-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_lift_one_id
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.lift_one_id
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:09.997135+00:00
-- url     : https://prove2.me/theorems/a32106c8-bac5-4be9-a3c9-82217fae2138
-- title:
--   Pullback Comparison: lift one id
-- statement:
--   The Pullback Comparison construction uses the lift one id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L93-L106

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

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.lift_one_id :
    (lift (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G) (𝟙 _)).left ≫ pφ₂ f G =
      pφ f G ≫ (lift (1 : G ⟶ G) (𝟙 G)).left := by sorry
