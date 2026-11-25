-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:15.773808+00:00
-- url     : https://prove2.me/theorems/f2af9af2-e7ee-44b9-88b9-c218161aa434
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of mem bea31bfbe550: P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of mem bea31b
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of mem bea31bfbe550 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of mem bea31bfbe550 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L163-L167

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
variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}
variable {c : A} {z : Fin m → D} {s : Finset D}

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550 {t : D} (ht : t ∈ s) : CombAfterPower c z s t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«CombAfterPower».«of_mem» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_mem_bea31bfbe550
