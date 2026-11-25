-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1
-- name    : P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:41.051457+00:00
-- url     : https://prove2.me/theorems/3dfaca71-e5cb-4dcc-941a-8fffc5eb03f7
-- title:
--   P2 M Ground Theory Heights  Heights slice CMUnmixed local c3dc3ab32cc1: P2 M Ground Theory Heights  Heights slice CMUnmixed local c3dc3ab32cc1
-- statement:
--   The P2 M Ground Theory Heights  Heights slice CMUnmixed local c3dc3ab32cc1 construction uses the P2 M Ground Theory Heights  Heights slice CMUnmixed local c3dc3ab32cc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceCMUnmixed.lean#L10-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceCMUnmixed.lean#L10-L106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCMUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMQuotientUnmixed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceCMUnmixed
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
open MvPolynomial Matrix ComplexSets IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1 (h : CMQuotientUnmixed.Statement) {R : Type} [CommRing R] [IsNoetherianRing R]
    (m : Ideal R) [m.IsPrime] {d : ℕ} (J : Ideal R) (ℓ : Fin d → R) (hℓ : ∀ i, ℓ i ∈ m)
    (B : Type) [CommRing B] [IsCohenMacaulayLocalRing B] (π : Localization.AtPrime m →+* B)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J.map (algebraMap R (Localization.AtPrime m)))
    (hB : ringKrullDim B = (d + 1 : ℕ))
    (hS : ringKrullDim (Localization.AtPrime m ⧸
      (J ⊔ Ideal.span (Set.range ℓ)).map (algebraMap R (Localization.AtPrime m))) = (1 : ℕ)) :
    ∀ P ∈ associatedPrimes R (R ⧸ (J ⊔ Ideal.span (Set.range ℓ))), P ≤ m →
      P ∈ (J ⊔ Ideal.span (Set.range ℓ)).minimalPrimes ∧ P ≠ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«sliceCMUnmixed_local» := P2M_GroundTheory_Heights__Heights_sliceCMUnmixed_local_c3dc3ab32cc1
