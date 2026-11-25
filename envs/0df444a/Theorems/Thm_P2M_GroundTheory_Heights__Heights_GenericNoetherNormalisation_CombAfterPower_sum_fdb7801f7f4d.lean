-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_sum_fdb7801f7f4d
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_sum_fdb7801f7f4d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:14.584132+00:00
-- url     : https://prove2.me/theorems/3c4c23e0-0df2-4ab4-8cfc-3bcdc17963dd
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power sum fdb7801f7f4d: P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power sum fdb7801f7f4d
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power sum fdb7801f7f4d construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power sum fdb7801f7f4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L154-L156

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_sum_fdb7801f7f4d {ι : Type*} (u : Finset ι) (F : ι → D)
    (h : ∀ i ∈ u, CombAfterPower c z s (F i)) : CombAfterPower c z s (∑ i ∈ u, F i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«CombAfterPower».«sum» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_sum_fdb7801f7f4d
