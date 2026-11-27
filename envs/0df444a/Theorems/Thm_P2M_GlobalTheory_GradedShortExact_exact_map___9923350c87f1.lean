-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GradedShortExact_exact_map___9923350c87f1
-- name    : P2M_GlobalTheory_GradedShortExact_exact_map___9923350c87f1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:43.730309+00:00
-- url     : https://prove2.me/theorems/b353af68-266c-5095-91a6-c075b2d1bdb3
-- title:
--   P2 M Global Theory Graded Short Exact exact map   9923350c87f1: P2 M Global Theory Graded Short Exact exact map   9923350c87f1
-- statement:
--   The P2 M Global Theory Graded Short Exact exact map   9923350c87f1 construction uses the P2 M Global Theory Graded Short Exact exact map   9923350c87f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L788-L791
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsAwayFracOfMemHomLoc.lean#L788-L791

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial CategoryTheory
universe u
noncomputable section
open GlobalTheory
open GradedHilbert
open GlobalTheory.GradedShortExact
variable {ι : Type} {R : Type u} [CommRing R]
  {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  [IsScalarTower R (MvPolynomial ι R) M]
  {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
  {P : Type u} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
  [IsScalarTower R (MvPolynomial ι R) P]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩]
  {𝒬 : ℤ → Submodule R P} [PolyGradedSMul ι 𝒬]
  {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P} (h : GradedShortExact ℳ 𝒩 𝒬 f g)
variable [LinearOrder ι]
variable [Decomposition ℳ] [Decomposition 𝒩] [Decomposition 𝒬]

theorem P2M_GlobalTheory_GradedShortExact_exact_map___9923350c87f1 (n : ℤ) (p : ℕ) :
    Function.Exact (grHMap h.graded_g n p).hom (h.δ n p).hom := by sorry

alias «GlobalTheory».«GradedShortExact».«exact_map_δ» := P2M_GlobalTheory_GradedShortExact_exact_map___9923350c87f1
