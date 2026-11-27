-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_exists_leadingCoeff_nagata_9a14b68b1291
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_exists_leadingCoeff_nagata_9a14b68b1291
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:24:39.053994+00:00
-- url     : https://prove2.me/theorems/16488c93-1093-4e51-9b01-a10506c12dc5
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation exists leading Coeff nagata 9a14b68b1291: P2 M Ground Theory Heights  Heights Generic Noether Normalisation exists leading Coeff nagat
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation exists leading Coeff nagata 9a14b68b1291 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation exists leading Coeff nagata 9a14b68b1291 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L87-L113

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
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_exists_leadingCoeff_nagata_9a14b68b1291 (fne : f ≠ 0) :
    ∃ c : A, c ≠ 0 ∧ (finSuccEquiv A n (nagataEquiv f f)).leadingCoeff = MvPolynomial.C c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«exists_leadingCoeff_nagata» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_exists_leadingCoeff_nagata_9a14b68b1291
