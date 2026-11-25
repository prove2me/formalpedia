-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:31:17.187517+00:00
-- url     : https://prove2.me/theorems/ad8712d6-f21b-4396-9d0d-8bfa1197854e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn of lt ec68d02ba4cc: P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn of lt ec68d02ba4cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn of lt ec68d02ba4cc construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn of lt ec68d02ba4cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L15-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDSq
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc {K : Finset (Fin n)} {j k : Fin n} (hj : j ∈ K) (hjk : j < k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDSq».«sgn_mul_sgn_of_lt» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_of_lt_ec68d02ba4cc
