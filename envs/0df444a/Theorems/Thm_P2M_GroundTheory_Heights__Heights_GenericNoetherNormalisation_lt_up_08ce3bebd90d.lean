-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_lt_up_08ce3bebd90d
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_lt_up_08ce3bebd90d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:14:35.871785+00:00
-- url     : https://prove2.me/theorems/e2516fd0-7160-4811-84b9-a01f20aba2d1
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation lt up 08ce3bebd90d: P2 M Ground Theory Heights  Heights Generic Noether Normalisation lt up 08ce3bebd90d
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation lt up 08ce3bebd90d construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation lt up 08ce3bebd90d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L37-L38

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
omit [IsDomain A]
variable {f v}

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_lt_up_08ce3bebd90d (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«lt_up» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_lt_up_08ce3bebd90d
