-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:13.430117+00:00
-- url     : https://prove2.me/theorems/c2c3fdaa-4359-4f69-9548-66986c501dbd
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pullback map left fst  894f6221002c: P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pullback map left fst  89
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pullback map left fst  894f6221002c construction uses the P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pullback map left fst  894f6221002c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L15-L18

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c {A B : Over S} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Pdiv».«PullbackComparison».«pullback_map_left_fst'» := P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullback_map_left_fst__894f6221002c
