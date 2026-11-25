-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_exists_quotient_primes_3a3083b0e3b1
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_exists_quotient_primes_3a3083b0e3b1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:03.821884+00:00
-- url     : https://prove2.me/theorems/02cabfc8-e81b-4b0b-b2bf-5a8462d713d9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Local Chart exists quotient primes 3a3083b0e3b1: P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Local Chart exists quotient primes 3a30
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Local Chart exists quotient primes 3a3083b0e3b1 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Blow Up Local Chart exists quotient primes 3a3083b0e3b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpOrderLe.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsBlowUpOrderLe.lean#L59-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_exists_quotient_primes_3a3083b0e3b1 {R : Type*} [CommRing R] {K : Type*} {ι : K → Type}
    {J : Type} {P : Ideal (MRing ι R)} {u : J → MRing ι R} {G' : Ideal (MRing (extIdx ι J) R)}
    (hG' : G'.IsPrime) (hQ : blowUpOf P u ≤ G') (hP : P ≤ G'.comap (liftForm (J := J))) :
    ∃ (G₀ : Ideal (MRing ι R ⧸ P)) (W₀ : Ideal (MRing (extIdx ι J) R ⧸ blowUpOf P u)),
      G₀.IsPrime ∧ W₀.IsPrime ∧ G₀.comap (Ideal.Quotient.mk P) = G'.comap (liftForm (J := J)) ∧
        W₀.comap (Ideal.Quotient.mk (blowUpOf P u)) = G' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«BlowUpLocalChart».«exists_quotient_primes» := P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_exists_quotient_primes_3a3083b0e3b1
