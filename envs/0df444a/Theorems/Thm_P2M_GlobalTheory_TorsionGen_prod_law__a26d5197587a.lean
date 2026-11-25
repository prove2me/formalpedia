-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorsionGen_prod_law__a26d5197587a
-- name    : P2M_GlobalTheory_TorsionGen_prod_law__a26d5197587a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:57:53.313854+00:00
-- url     : https://prove2.me/theorems/f0ae23a0-cfe7-4d6f-8416-e12fe29c75d0
-- title:
--   P2 M Global Theory Torsion Gen prod law  a26d5197587a: P2 M Global Theory Torsion Gen prod law  a26d5197587a
-- statement:
--   The P2 M Global Theory Torsion Gen prod law  a26d5197587a construction uses the P2 M Global Theory Torsion Gen prod law  a26d5197587a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L118-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L118-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdCocycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionGen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

theorem P2M_GlobalTheory_TorsionGen_prod_law__a26d5197587a {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((lift x (lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by sorry

alias «GlobalTheory».«TorsionGen».«prod_law₁» := P2M_GlobalTheory_TorsionGen_prod_law__a26d5197587a
