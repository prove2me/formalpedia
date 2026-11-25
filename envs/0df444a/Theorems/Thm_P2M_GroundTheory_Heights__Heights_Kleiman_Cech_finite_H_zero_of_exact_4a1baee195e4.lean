-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:21.715798+00:00
-- url     : https://prove2.me/theorems/20d6a2f7-09a3-4f5b-892d-f5a19be90da4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech finite H zero of exact 4a1baee195e4: P2 M Ground Theory Heights  Heights Kleiman Cech finite H zero of exact 4a1baee195e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech finite H zero of exact 4a1baee195e4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech finite H zero of exact 4a1baee195e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/FiniteHZeroOfExact.lean#L23-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/FiniteHZeroOfExact.lean#L23-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_FiniteHZeroOfExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w v₁ v₂ v₃
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {A : Cell U → Type v₁} [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)]
  {B : Cell U → Type v₂} [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
  {C : Cell U → Type v₃} [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4 [IsNoetherianRing R]
    (ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J) (ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J)
    (ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (ι : ∀ I, A I →ₗ[R] B I) (q : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hq : ∀ I J h m, q J (ρB I J h m) = ρC I J h (q I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (q I))
    (hex : ∀ I b, q I b = 0 ↔ ∃ a, ι I a = b)
    (hB : Module.Finite R (H B ρB 0)) (hA : Module.Finite R (H A ρA 1)) :
    Module.Finite R (H C ρC 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«finite_H_zero_of_exact» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_finite_H_zero_of_exact_4a1baee195e4
