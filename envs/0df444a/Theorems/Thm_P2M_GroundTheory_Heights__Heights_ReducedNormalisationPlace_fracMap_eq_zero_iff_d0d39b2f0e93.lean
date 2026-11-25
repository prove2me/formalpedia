-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93
-- name    : P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:06:24.754197+00:00
-- url     : https://prove2.me/theorems/8bfe0cea-4e4e-5e5d-ba0c-a5009cb98132
-- title:
--   P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map eq zero iff d0d39b2f0e93: P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map eq zero iff d0d39b2f0e93
-- statement:
--   The P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map eq zero iff d0d39b2f0e93 construction uses the P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map eq zero iff d0d39b2f0e93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L21-L26

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

theorem P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93 {C : Type*} [CommRing C] [IsDomain B] [IsDomain C] (π : A →+* B) (π' : A →+* C)
    (hker : RingHom.ker π ∈ minimalPrimes A) (hker' : RingHom.ker π' ∈ minimalPrimes A)
    (h : RingHom.ker π = RingHom.ker π') (z : FractionRing A) :
    fracMap π hker z = 0 ↔ fracMap π' hker' z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReducedNormalisationPlace».«fracMap_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_eq_zero_iff_d0d39b2f0e93
