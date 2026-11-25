-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:26:12.901856+00:00
-- url     : https://prove2.me/theorems/8bf45029-d477-4531-a8af-1accbe219738
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place exists localization ring Equiv bf72767a7e08: P2 M Ground Theory Heights  Heights Minimal Prime Place exists localization ring Equiv bf72767a7e08
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place exists localization ring Equiv bf72767a7e08 construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place exists localization ring Equiv bf72767a7e08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L160-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L160-L194

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ) (ε : R) (hε1 : φ ε = 1) (hε : ∀ z, φ z = 0 → ε * z = 0) (P' : Ideal S)
    [P'.IsPrime] :
    ∃ E : Localization.AtPrime (P'.comap φ) ≃+* Localization.AtPrime P',
      ∀ r, E (algebraMap R _ r) = algebraMap S _ (φ r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«exists_localization_ringEquiv» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_exists_localization_ringEquiv_bf72767a7e08
