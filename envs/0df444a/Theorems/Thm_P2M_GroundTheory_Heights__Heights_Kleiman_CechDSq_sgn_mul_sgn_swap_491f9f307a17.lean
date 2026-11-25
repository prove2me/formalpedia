-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:12.484073+00:00
-- url     : https://prove2.me/theorems/6769ef00-de62-49c3-a988-8f77684f2132
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn swap 491f9f307a17: P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn swap 491f9f307a17
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn swap 491f9f307a17 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech DSq sgn mul sgn swap 491f9f307a17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechDSq.lean#L30-L34

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17 {K : Finset (Fin n)} {j k : Fin n} (hk : k ∈ K) (hj : j ∈ K) (hne : j ≠ k) :
    Cech.sgn K k * Cech.sgn (K.erase k) j = -(Cech.sgn K j * Cech.sgn (K.erase j) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CechDSq».«sgn_mul_sgn_swap» := P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17
