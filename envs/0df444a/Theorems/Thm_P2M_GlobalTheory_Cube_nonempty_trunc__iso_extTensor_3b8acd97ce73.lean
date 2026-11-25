-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73
-- name    : P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:08.501644+00:00
-- url     : https://prove2.me/theorems/7d108223-4bd2-43f5-852b-ca07692b38c4
-- title:
--   P2 M Global Theory Cube nonempty trunc  iso ext Tensor 3b8acd97ce73: P2 M Global Theory Cube nonempty trunc  iso ext Tensor 3b8acd97ce73
-- statement:
--   The P2 M Global Theory Cube nonempty trunc  iso ext Tensor 3b8acd97ce73 construction uses the P2 M Global Theory Cube nonempty trunc  iso ext Tensor 3b8acd97ce73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L575-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L575-L619

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
omit [Finite ι] [Finite κ]
variable {A B}
variable (A B)

theorem P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73 (C : Cube.{v} (ι ⊕ₗ κ) K)
    (μ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      A.obj s ⊗[K] B.obj t →ₗ[K] C.obj (sumVertex s t))
    (hμ : ∀ s t hs ht, Function.Bijective (μ s t hs ht))
    (hnat : ∀ {s s' : Finset ι} {t t' : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
      (h : s ⊆ s') (h' : t ⊆ t') (a : A.obj s) (b : B.obj t),
      μ s' t' (hs.mono h) (ht.mono h') (res A h a ⊗ₜ res B h' b) =
        res C (sumVertex_mono h h') (μ s t hs ht (a ⊗ₜ b))) :
    Nonempty (trunc₂ C ≅ trunc₂ (extTensor A B)) := by sorry

alias «GlobalTheory».«Cube».«nonempty_trunc₂_iso_extTensor» := P2M_GlobalTheory_Cube_nonempty_trunc__iso_extTensor_3b8acd97ce73
