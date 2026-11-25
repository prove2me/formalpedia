-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:55:28.913277+00:00
-- url     : https://prove2.me/theorems/8d6baade-3295-4fe3-a8d4-e625d512b3c4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one of exact 45ae9e3bf583: P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one of exact 45ae9e3bf583
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one of exact 45ae9e3bf583 construction uses the P2 M Ground Theory Heights  Heights Kleiman Quot Trans subsingleton H one of exact 45ae9e3bf583 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L79-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PQuotTrans.lean#L79-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotTrans
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583 {A B C : Cell U → Type v}
    [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)] [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
    {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J} {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
    {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
    (ι : ∀ I, A I →ₗ[R] B I) (π : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hπ : ∀ I J h m, π J (ρB I J h m) = ρC I J h (π I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (π I))
    (hex : ∀ I b, π I b = 0 → ∃ a, ι I a = b)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (hA : Subsingleton (Cech.H A ρA 1)) (hC : Subsingleton (Cech.H C ρC 1)) :
    Subsingleton (Cech.H B ρB 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«QuotTrans».«subsingleton_H_one_of_exact» := P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583
