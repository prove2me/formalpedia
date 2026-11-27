-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbLaw_cechLB_homology_equiv_trunc__da0132300080
-- name    : P2M_GlobalTheory_AbLaw_cechLB_homology_equiv_trunc__da0132300080
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:50.94629+00:00
-- url     : https://prove2.me/theorems/20daf897-1fb6-5cdc-983e-a2eac2f4439f
-- title:
--   P2 M Global Theory Ab Law cech LB homology equiv trunc  da0132300080: P2 M Global Theory Ab Law cech LB homology equiv trunc  da0132300080
-- statement:
--   The P2 M Global Theory Ab Law cech LB homology equiv trunc  da0132300080 construction uses the P2 M Global Theory Ab Law cech LB homology equiv trunc  da0132300080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L67-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsAffineOpenBiInfOfLe.lean#L67-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineOpenBiInfOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw

theorem P2M_GlobalTheory_AbLaw_cechLB_homology_equiv_trunc__da0132300080 :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ⨆ i, U i = ⊤ → ⨆ j, W j = ⊤ → (∀ i V, IsAffineOpen V → IsAffineOpen (U i ⊓ V)) → (∀ j V, IsAffineOpen V → IsAffineOpen (W j ⊓ V)) → (∀ i j, IsAffineOpen (U i ⊓ W j)) → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cubeComplex (Cube.trunc₂ (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)))).homology (n + 2)) := by sorry

alias «GlobalTheory».«AbLaw».«cechLB_homology_equiv_trunc₂» := P2M_GlobalTheory_AbLaw_cechLB_homology_equiv_trunc__da0132300080
