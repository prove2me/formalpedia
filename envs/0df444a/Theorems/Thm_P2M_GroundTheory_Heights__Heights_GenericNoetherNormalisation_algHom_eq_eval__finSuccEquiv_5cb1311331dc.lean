-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_algHom_eq_eval__finSuccEquiv_5cb1311331dc
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_algHom_eq_eval__finSuccEquiv_5cb1311331dc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:42.289797+00:00
-- url     : https://prove2.me/theorems/093014dc-9bc9-47a8-922e-3b0147ed28ce
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation alg Hom eq eval  fin Succ Equiv 5cb1311331dc: P2 M Ground Theory Heights  Heights Generic Noether Normalisation alg Hom eq eval  fin S
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation alg Hom eq eval  fin Succ Equiv 5cb1311331dc construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation alg Hom eq eval  fin Succ Equiv 5cb1311331dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L190-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L190-L200

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
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
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_algHom_eq_eval__finSuccEquiv_5cb1311331dc {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {n : ℕ}
    (ψ : MvPolynomial (Fin (n + 1)) A →ₐ[A] D) (P : MvPolynomial (Fin (n + 1)) A) :
    ψ P = (finSuccEquiv A n P).eval₂
      (MvPolynomial.aeval (R := A) (fun i : Fin n ↦ ψ (X i.succ))).toRingHom (ψ (X 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«algHom_eq_eval₂_finSuccEquiv» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_algHom_eq_eval__finSuccEquiv_5cb1311331dc
