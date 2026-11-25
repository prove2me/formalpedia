-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5
-- name    : P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:38:50.082092+00:00
-- url     : https://prove2.me/theorems/00c1a74a-3c55-48b7-a2bb-6342de219496
-- title:
--   P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map mk  eq zero iff b3c2a6f3b1b5: P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map mk  eq zero iff b3c2a6f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map mk  eq zero iff b3c2a6f3b1b5 construction uses the P2 M Ground Theory Heights  Heights Reduced Normalisation Place frac Map mk  eq zero iff b3c2a6f3b1b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L16-L19

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

theorem P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5 [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A)
    (u : nonZeroDivisors A) :
    fracMap π hker (IsLocalization.mk' (FractionRing A) a u) = 0 ↔ a ∈ RingHom.ker π := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReducedNormalisationPlace».«fracMap_mk'_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_fracMap_mk__eq_zero_iff_b3c2a6f3b1b5
