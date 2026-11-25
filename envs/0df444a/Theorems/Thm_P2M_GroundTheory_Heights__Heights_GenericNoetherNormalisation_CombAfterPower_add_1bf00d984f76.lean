-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:31:27.555309+00:00
-- url     : https://prove2.me/theorems/ef116391-fff3-436e-9ddf-eeec1cfe9c21
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power add 1bf00d984f76: P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power add 1bf00d984f76
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power add 1bf00d984f76 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power add 1bf00d984f76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L135-L144

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76 {d e : D} (hd : CombAfterPower c z s d) (he : CombAfterPower c z s e) :
    CombAfterPower c z s (d + e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«CombAfterPower».«add» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_add_1bf00d984f76
