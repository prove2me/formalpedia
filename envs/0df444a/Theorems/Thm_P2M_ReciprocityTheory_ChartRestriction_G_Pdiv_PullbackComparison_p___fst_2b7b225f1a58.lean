-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___fst_2b7b225f1a58
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___fst_2b7b225f1a58
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:31.319804+00:00
-- url     : https://prove2.me/theorems/2956b0c7-3f32-4e36-9a9c-ecc4e479ed53
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   fst 2b7b225f1a58: P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   fst 2b7b225f1a58
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   fst 2b7b225f1a58 construction uses the P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   fst 2b7b225f1a58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L25-L27

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___fst_2b7b225f1a58 : pφ₂ f G ≫ (fst G G).left = (fst ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Pdiv».«PullbackComparison».«pφ₂_fst» := P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___fst_2b7b225f1a58
