-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prime_map_of_prime_795d521bbf73
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prime_map_of_prime_795d521bbf73
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:16.303095+00:00
-- url     : https://prove2.me/theorems/6e84ead7-b705-5684-a474-90f9f4505a1f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime map of prime 795d521bbf73: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime m
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime map of prime 795d521bbf73 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets prime map of prime 795d521bbf73 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean#L13-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prime_map_of_prime_795d521bbf73 {R S : Type*} [CommRing R] [CommRing S] (Ψ : R →+* S) {ω : R} (hω : Prime ω)
    (hne : Ψ ω ≠ 0) (hsurj : ∀ g : S, ∃ (Q : S) (p : R), g = Ψ ω * Q + Ψ p)
    (hdvd : ∀ p : R, Ψ ω ∣ Ψ p → ω ∣ p) : Prime (Ψ ω) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«prime_map_of_prime» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_prime_map_of_prime_795d521bbf73
