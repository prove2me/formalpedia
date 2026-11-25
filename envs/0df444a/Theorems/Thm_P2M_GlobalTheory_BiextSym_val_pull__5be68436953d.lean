-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BiextSym_val_pull__5be68436953d
-- name    : P2M_GlobalTheory_BiextSym_val_pull__5be68436953d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:59.215607+00:00
-- url     : https://prove2.me/theorems/2fea76c5-8e2f-4f30-86dc-be947847beed
-- title:
--   P2 M Global Theory Biext Sym val pull  5be68436953d: P2 M Global Theory Biext Sym val pull  5be68436953d
-- statement:
--   The P2 M Global Theory Biext Sym val pull  5be68436953d construction uses the P2 M Global Theory Biext Sym val pull  5be68436953d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawProduct.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawProduct.lean#L94-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct
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
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem P2M_GlobalTheory_BiextSym_val_pull__5be68436953d {X : Scheme.{0}} {P : LB X} {K : Type} [Fintype K] {B C : Over S} {φ : K → ((B ⊗ C).left ⟶ X)}
    {ε : K → ℤ} (u : LB.Gen (LB.LinComb P φ ε)) {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J} (hJ : Good P z J)
    (a : T ⟶ B) (b : T ⟶ C) :
    val (LB.pullGen P φ ε u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J := by sorry

alias «GlobalTheory».«BiextSym».«val_pull₂» := P2M_GlobalTheory_BiextSym_val_pull__5be68436953d
