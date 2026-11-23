-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_one_left_p__16057314fd74
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_one_left_p__16057314fd74
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:02.356321+00:00
-- url     : https://prove2.me/theorems/9efc31d3-3b47-40c7-881a-294299f39f34
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison one left p  16057314fd74: P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison one left p  16057314fd74
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison one left p  16057314fd74 construction uses the P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison one left p  16057314fd74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L54-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L54-L69

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_one_left_p__16057314fd74 :
    (1 : (Over.pullback f).obj G ⟶ (Over.pullback f).obj G).left ≫ pφ f G =
      pφ f G ≫ (1 : G ⟶ G).left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Pdiv».«PullbackComparison».«one_left_pφ» := P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_one_left_p__16057314fd74
