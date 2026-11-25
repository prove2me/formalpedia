-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_swapFirstTwo_proj_prod
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.swapFirstTwo_proj_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:44:19.737846+00:00
-- url     : https://prove2.me/theorems/e82677c1-4675-4965-8b17-da50a041b315
-- title:
--   Cube Coordinate Sums: swap First Two proj prod
-- statement:
--   The Cube Coordinate Sums construction uses the swap First Two proj prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L110-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_CubeFaceMiddleProjProd
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums
open Semi
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.swapFirstTwo_proj_prod (j : Fin 3) :
    lift (x3 H 1) (lift (x3 H 0) (x3 H 2)) ≫ x3 H j = ∏ l ∈ swapFirstTwoSubsets j, x3 H l := by sorry
