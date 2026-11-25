-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:35:43.17284+00:00
-- url     : https://prove2.me/theorems/c41c19ec-fe46-48a8-bfb9-196aad22c0bb
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place is Integral mul of frac Map 31178a133ad5: P2 M Ground Theory Heights  Heights Minimal Prime Place is Integral mul of frac Map 31178a133ad5
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place is Integral mul of frac Map 31178a133ad5 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place is Integral mul of frac Map 31178a133ad5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L133-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMinimalPrimePlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
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
open MvPolynomial ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.MinimalPrimePlace
variable {A B : Type*} [CommRing A] [CommRing B]

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5 [IsDomain B] (π : A →+* B) (hπ : Function.Surjective π)
    (hker : RingHom.ker π ∈ minimalPrimes A) {e x : FractionRing A} (he1 : fracMap π hker e = 1)
    (hek : ∀ z, fracMap π hker z = 0 → e * z = 0) (hx : IsIntegral B (fracMap π hker x)) :
    IsIntegral A (e * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«isIntegral_mul_of_fracMap» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_isIntegral_mul_of_fracMap_31178a133ad5
