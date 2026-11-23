-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_CubePf_CubeCoordinateSums_fam_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.fam_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:46.95549+00:00
-- url     : https://prove2.me/theorems/f7d612df-3427-4a00-aabf-cb9b452b443c
-- title:
--   Cube Coordinate Sums: fam eq
-- statement:
--   The Cube Coordinate Sums construction uses the fam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/CubeFaceMiddleProjProd.lean#L72-L81

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

theorem ReciprocityTheory.ChartRestriction.G.Out.CubePf.CubeCoordinateSums.fam_eq {T : Over S} (a : T ⟶ G3 H) {m : ℕ} (y : Fin m → (T ⟶ H))
    (A : Fin 3 → Finset (Fin m)) (hA : ∀ i, a ≫ x3 H i = ∏ j ∈ A i, y j)
    (hdis : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) (k : thK) :
    a.left ≫ thφ H (x3 H) k = (∏ j ∈ k.down.biUnion A, y j).left := by sorry
