-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37
-- name    : P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:02.725248+00:00
-- url     : https://prove2.me/theorems/478575c4-b4d9-4c74-9efd-4c096858434b
-- title:
--   P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of smul ec967148cc37: P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of smul ec96
-- statement:
--   The P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of smul ec967148cc37 construction uses the P2 M Ground Theory Heights  Heights Generic Noether Normalisation Comb After Power of smul ec967148cc37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGenericNoetherNormalisation.lean#L158-L161

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

theorem P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37 {d : D} (h : CombAfterPower c z s (c • d)) :
    CombAfterPower c z s d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GenericNoetherNormalisation».«CombAfterPower».«of_smul» := P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_of_smul_ec967148cc37
