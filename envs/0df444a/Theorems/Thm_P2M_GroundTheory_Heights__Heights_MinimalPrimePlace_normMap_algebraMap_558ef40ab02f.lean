-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
-- name    : P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:46.633382+00:00
-- url     : https://prove2.me/theorems/81f8e492-aa9b-4e47-96c0-ef4d33fbb85d
-- title:
--   P2 M Ground Theory Heights  Heights Minimal Prime Place norm Map algebra Map 558ef40ab02f: P2 M Ground Theory Heights  Heights Minimal Prime Place norm Map algebra Map 558ef40ab02f
-- statement:
--   The P2 M Ground Theory Heights  Heights Minimal Prime Place norm Map algebra Map 558ef40ab02f construction uses the P2 M Ground Theory Heights  Heights Minimal Prime Place norm Map algebra Map 558ef40ab02f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMinimalPrimePlace.lean#L154-L158

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

theorem P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f [IsDomain B] (π : A →+* B) (hker : RingHom.ker π ∈ minimalPrimes A) (a : A) :
    normMap π hker (algebraMap A (integralClosure A (FractionRing A)) a) =
      algebraMap B (integralClosure B (FractionRing B)) (π a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MinimalPrimePlace».«normMap_algebraMap» := P2M_GroundTheory_Heights__Heights_MinimalPrimePlace_normMap_algebraMap_558ef40ab02f
