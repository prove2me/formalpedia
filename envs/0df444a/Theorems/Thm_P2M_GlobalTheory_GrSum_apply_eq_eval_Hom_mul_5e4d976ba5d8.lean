-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8
-- name    : P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:19.175077+00:00
-- url     : https://prove2.me/theorems/d71e8780-34dd-587e-854f-a9005c233eae
-- title:
--   P2 M Global Theory Gr Sum apply eq eval Hom mul 5e4d976ba5d8: P2 M Global Theory Gr Sum apply eq eval Hom mul 5e4d976ba5d8
-- statement:
--   The P2 M Global Theory Gr Sum apply eq eval Hom mul 5e4d976ba5d8 construction uses the P2 M Global Theory Gr Sum apply eq eval Hom mul 5e4d976ba5d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulOfTwCoord.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulOfTwCoord.lean#L13-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulOfTwCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory

theorem P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8 {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by sorry

alias «GlobalTheory».«GrSum».«apply_eq_eval₂Hom_mul» := P2M_GlobalTheory_GrSum_apply_eq_eval_Hom_mul_5e4d976ba5d8
