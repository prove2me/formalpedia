-- Prove2me | Theorems.Thm_P2M_GlobalTheory_augCot_properties__915c04dc6773
-- name    : P2M_GlobalTheory_augCot_properties__915c04dc6773
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:32.859804+00:00
-- url     : https://prove2.me/theorems/2b6f4d51-96bf-4749-953a-c3836936fe64
-- title:
--   P2 M Global Theory aug Cot properties  915c04dc6773: P2 M Global Theory aug Cot properties  915c04dc6773
-- statement:
--   The P2 M Global Theory aug Cot properties  915c04dc6773 construction uses the P2 M Global Theory aug Cot properties  915c04dc6773 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L804-L878
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L804-L878

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open AugCot

theorem P2M_GlobalTheory_augCot_properties__915c04dc6773.{u} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (ε : A →ₐ[R] R) :

    (∀ a : A, d ε a = (RingHom.ker ε).toCotangent
      ⟨a - algebraMap R A (ε a), by simp [RingHom.mem_ker]⟩) ∧

    (letI : Algebra A R := (ε : A →+* R).toAlgebra
     ∃ e : AugCot ε ≃ₗ[R] R ⊗[A] Ω[A⁄R],
      ∀ a, e (d ε a) = 1 ⊗ₜ KaehlerDifferential.D R A a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N],
      letI : Module A N := Module.compHom N (ε : A →+* R)
      haveI : IsScalarTower R A N := isScalarTower_of_smul_eq ε fun _ _ => rfl
      ∃ e : Derivation R A N ≃ₗ[R] (AugCot ε →ₗ[R] N), ∀ D a, e D (d ε a) = D a) ∧

    (∀ (N : Type u) [AddCommGroup N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N],
      ∃ e : {φ : A →ₐ[R] TrivSqZeroExt R N // (TrivSqZeroExt.fstHom R R N).comp φ = ε} ≃
        (AugCot ε →ₗ[R] N), ∀ φ a, e φ (d ε a) = (φ.1 a).snd) ∧

    (∀ (R' : Type u) [CommRing R'] [Algebra R R'],
      (∀ r a, baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a)) ∧
      ∃ e : R' ⊗[R] AugCot ε ≃ₗ[R'] AugCot (baseChangeAug R' ε),
        ∀ r a, e (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a)) ∧

    (map (AlgHom.id R A) (AlgHom.comp_id ε) = LinearMap.id) ∧
    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R) (φ : A →ₐ[R] B)
      (h : εB.comp φ = ε),
      (∀ a, map φ h (d ε a) = d εB (φ a)) ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (εC : C →ₐ[R] R) (ψ : B →ₐ[R] C)
        (h' : εC.comp ψ = εB) (h'' : εC.comp (ψ.comp φ) = ε),
        map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h) ∧

      ((φ : A →+* B).Etale → Function.Bijective (map φ h)) ∧

      (Function.Surjective φ →
        (∀ x : RingHom.ker φ, kerMap φ h x = (RingHom.ker ε).toCotangent ⟨x, ker_le φ h x.2⟩) ∧
        Function.Exact (kerMap φ h) (map φ h) ∧ Function.Surjective (map φ h))) ∧

    (∀ (f : A) (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
      [IsLocalization.Away f B],
      (IsUnit (ε f) → ∃ εB : B →ₐ[R] R, εB.comp (IsScalarTower.toAlgHom R A B) = ε) ∧
      ∀ (εB : B →ₐ[R] R) (h : εB.comp (IsScalarTower.toAlgHom R A B) = ε),
        Function.Bijective (map _ h)) ∧

    (∀ (B : Type u) [CommRing B] [Algebra R B] (εB : B →ₐ[R] R),
      ∃ e : AugCot (Algebra.TensorProduct.productMap ε εB) ≃ₗ[R] AugCot ε × AugCot εB,
        ∀ a b, e (d _ (a ⊗ₜ b)) = (εB b • d ε a, ε a • d εB b)) ∧

    (Algebra.Smooth R A → Module.Finite R (AugCot ε) ∧ Module.Projective R (AugCot ε) ∧
      (IsLocalRing R → Module.Free R (AugCot ε))) ∧
    (Algebra.IsStandardSmooth R A → Module.Free R (AugCot ε)) ∧
    (∀ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A →
      Nonempty (Module.Basis (Fin n) R (AugCot ε))) ∧
    (∀ n : ℕ, AlgebraicGeometry.SmoothOfRelativeDimension n
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R A))) →
      Algebra.Smooth R A ∧ (∀ p : PrimeSpectrum R, Module.rankAtStalk (AugCot ε) p = n) ∧
      (IsLocalRing R → Nonempty (Module.Basis (Fin n) R (AugCot ε)))) := by sorry

alias «GlobalTheory».«augCot_properties».«» := P2M_GlobalTheory_augCot_properties__915c04dc6773
