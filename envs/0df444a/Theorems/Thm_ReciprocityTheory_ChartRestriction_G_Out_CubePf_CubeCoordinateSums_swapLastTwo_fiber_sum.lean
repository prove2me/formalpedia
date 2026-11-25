-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_swapLastTwo_fiber_sum
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.swapLastTwo_fiber_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:30.343803+00:00
-- url     : https://prove2.me/theorems/7a3e9239-0acf-5933-9758-ac09321dffed
-- title:
--   Cube Coordinate Sums: swap Last Two fiber sum
-- statement:
--   The Cube Coordinate Sums construction uses the swap Last Two fiber sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L123-L126

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

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.swapLastTwo_fiber_sum : ∀ J₀ : Finset (Fin 3),
    (∑ k : thK, if k.down = J₀ then thε k else 0) =
      ∑ k : thK, if k.down.biUnion swapLastTwoSubsets = J₀ then thε k else 0 := by sorry
