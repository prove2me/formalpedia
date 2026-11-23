-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:59.309282+00:00
-- url     : https://prove2.me/theorems/e292c5d5-56ae-4079-821a-f8df90b26c24
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   snd 39b6d2e321d1: P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   snd 39b6d2e321d1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   snd 39b6d2e321d1 construction uses the P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison p   snd 39b6d2e321d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/AdelicGL2ExtOfLocalComponents.lean#L29-L31

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1 : pφ₂ f G ≫ (snd G G).left = (snd ((Over.pullback f).obj G) ((Over.pullback f).obj G)).left ≫ pφ f G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Pdiv».«PullbackComparison».«pφ₂_snd» := P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_p___snd_39b6d2e321d1
