-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_leadingCoeff_finSuccEquiv_nagata_9f1530c3b78a
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_leadingCoeff_finSuccEquiv_nagata_9f1530c3b78a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:11.073814+00:00
-- url     : https://prove2.me/theorems/9697c135-3cf0-4a84-a4d5-c2fa41b022b2
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation leading Coeff fin Succ Equiv nagata 9f1530c3b78a: P2 M Ground Theory Heights  Heights Generic Noether Normalisation leading Coeff fin
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation leading Coeff fin Succ Equiv nagata 9f1530c3b78a construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation leading Coeff fin Succ Equiv nagata 9f1530c3b78a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L69-L85

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_leadingCoeff_finSuccEquiv_nagata_9f1530c3b78a :
    (finSuccEquiv A n ((nagataEquiv f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap A _ (coeff v f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«leadingCoeff_finSuccEquiv_nagata» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_leadingCoeff_finSuccEquiv_nagata_9f1530c3b78a
