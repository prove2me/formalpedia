-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:47.219127+00:00
-- url     : https://prove2.me/theorems/cd73dd7b-95e9-4708-96f4-038111954185
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul sgn erase swap 5eea5c9c3658: P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul sgn erase swap 5eea5c9c3658
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul sgn erase swap 5eea5c9c3658 construction uses the P2 M Ground Theory Heights  Heights Kleiman Surjective Closed sgn mul sgn erase swap 5eea5c9c3658 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L21-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSurjectiveClosed.lean#L21-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658 {L : Finset (Fin n)} {j k : Fin n} (hj : j ∈ L) (hk : k ∈ L)
    (hjk : j ≠ k) :
    Cech.sgn L j * Cech.sgn (L.erase j) k = -(Cech.sgn L k * Cech.sgn (L.erase k) j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SurjectiveClosed».«sgn_mul_sgn_erase_swap» := P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658
