-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_sum_r_mul_ne_98623272d7f8
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_sum_r_mul_ne_98623272d7f8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:30.607397+00:00
-- url     : https://prove2.me/theorems/88444d98-c0a8-4fc0-9397-1856cddd2b77
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation sum r mul ne 98623272d7f8: P2 M Ground Theory Heights  Heights Generic Noether Normalisation sum r mul ne 98623272d7f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation sum r mul ne 98623272d7f8 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation sum r mul ne 98623272d7f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L40-L42

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_sum_r_mul_ne_98623272d7f8 (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«sum_r_mul_ne» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_sum_r_mul_ne_98623272d7f8
