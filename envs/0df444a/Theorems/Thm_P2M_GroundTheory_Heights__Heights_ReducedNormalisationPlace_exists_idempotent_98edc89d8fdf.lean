-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf
-- name    : P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:51.395892+00:00
-- url     : https://prove2.me/theorems/f1133d03-714c-4e58-832a-844dda3b1f7c
-- title:
--   P2 M Ground Theory Heights  Heights Reduced Normalisation Place exists idempotent 98edc89d8fdf: P2 M Ground Theory Heights  Heights Reduced Normalisation Place exists idempotent 98edc89d8fdf
-- statement:
--   The P2 M Ground Theory Heights  Heights Reduced Normalisation Place exists idempotent 98edc89d8fdf construction uses the P2 M Ground Theory Heights  Heights Reduced Normalisation Place exists idempotent 98edc89d8fdf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L35-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L35-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
open GroundTheory.Heights₂.Heights.ReducedNormalisationPlace
variable {A B : Type*} [CommRing A] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf [IsNoetherianRing A] [IsReduced A] (p : Ideal A) (hp : p ∈ minimalPrimes A) :
    ∃ e : integralClosure A (FractionRing A), ∀ (B : Type) [CommRing B] [IsDomain B] (π : A →+* B),
      Function.Surjective π → ∀ hker : RingHom.ker π = p,
        fracMap π (by rw [hker]; exact hp) e = 1 ∧
          ∀ z, fracMap π (by rw [hker]; exact hp) z = 0 → (e : FractionRing A) * z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReducedNormalisationPlace».«exists_idempotent» := P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_exists_idempotent_98edc89d8fdf
