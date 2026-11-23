-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_cocycle_sameSum
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.cocycle_sameSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:10.658915+00:00
-- url     : https://prove2.me/theorems/06b7ad24-e5e1-477e-abfd-5d68a04b6113
-- title:
--   Cube Pf: cocycle same Sum
-- statement:
--   The Cube Pf construction uses the cocycle same Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L220-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L220-L250

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi CubeCoordinateSums
variable {S : Scheme.{0}} (H : Over S) [GrpObj H] [IsCommMonObj H]

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.cocycle_sameSum :
    LB.SameSum
      (Sum.elim (fun k => (lift (padd H (x4 H 0) (x4 H 1)) (lift (x4 H 2) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 0) (lift (x4 H 1) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε)
      (Sum.elim (fun k => (lift (x4 H 0) (lift (padd H (x4 H 1) (x4 H 2)) (x4 H 3))).left ≫
          thφ H (x3 H) k)
        (fun k => (lift (x4 H 1) (lift (x4 H 2) (x4 H 3))).left ≫ thφ H (x3 H) k))
      (Sum.elim thε thε) := by sorry
