-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_combAfterPower_pow_9229b1bc7d44
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_combAfterPower_pow_9229b1bc7d44
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:52.903565+00:00
-- url     : https://prove2.me/theorems/9c21d109-6e3d-45e7-b479-1c2220817e6a
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation comb After Power pow 9229b1bc7d44: P2 M Ground Theory Heights  Heights Generic Noether Normalisation comb After Power pow 9229b1bc7d44
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation comb After Power pow 9229b1bc7d44 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation comb After Power pow 9229b1bc7d44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L169-L186

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_combAfterPower_pow_9229b1bc7d44 [DecidableEq D] (w : D) (N : ℕ) (b : ℕ → MvPolynomial (Fin m) A)
    (hrel : c • w ^ N = ∑ i ∈ Finset.range N, aeval z (b i) * w ^ i) (j : ℕ) :
    CombAfterPower c z ((Finset.range N).image (fun i ↦ w ^ i)) (w ^ j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«combAfterPower_pow» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_combAfterPower_pow_9229b1bc7d44
