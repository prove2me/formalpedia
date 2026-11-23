-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_sameSum_of_factor_loc
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.sameSum_of_factor_loc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:45:28.084461+00:00
-- url     : https://prove2.me/theorems/ef8ab64c-5080-4c5c-9311-42488fcb2a6f
-- title:
--   Cube Coordinate Sums: same Sum of factor loc
-- statement:
--   The Cube Coordinate Sums construction uses the same Sum of factor loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L18-L42

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

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.sameSum_of_factor_loc {Y X : Scheme.{0}} {K K' J : Type} [Fintype K] [Fintype K']
    [Fintype J] [DecidableEq J] (P : J → (Y ⟶ X)) (f : K → J) (f' : K' → J) (ε : K → ℤ)
    (ε' : K' → ℤ)
    (h : ∀ j₀ : J, (∑ k, if f k = j₀ then ε k else 0) = ∑ k', if f' k' = j₀ then ε' k' else 0) :
    LB.SameSum (fun k => P (f k)) ε (fun k' => P (f' k')) ε' := by sorry
