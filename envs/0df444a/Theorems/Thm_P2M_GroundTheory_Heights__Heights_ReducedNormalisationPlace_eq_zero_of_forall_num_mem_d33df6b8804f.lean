-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f
-- name    : P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:26.560933+00:00
-- url     : https://prove2.me/theorems/433338e0-e9ae-4c98-8066-8e17f4b2bae0
-- title:
--   P2 M Ground Theory Heights  Heights Reduced Normalisation Place eq zero of forall num mem d33df6b8804f: P2 M Ground Theory Heights  Heights Reduced Normalisation Place eq zero of forall num mem d33df6
-- statement:
--   The P2 M Ground Theory Heights  Heights Reduced Normalisation Place eq zero of forall num mem d33df6b8804f construction uses the P2 M Ground Theory Heights  Heights Reduced Normalisation Place eq zero of forall num mem d33df6b8804f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean#L28-L33

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

theorem P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f [IsReduced A] (z : FractionRing A)
    (h : ∀ p ∈ minimalPrimes A, ∀ (a : A) (u : nonZeroDivisors A),
      z = IsLocalization.mk' (FractionRing A) a u → a ∈ p) : z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReducedNormalisationPlace».«eq_zero_of_forall_num_mem» := P2M_GroundTheory_Heights__Heights_ReducedNormalisationPlace_eq_zero_of_forall_num_mem_d33df6b8804f
