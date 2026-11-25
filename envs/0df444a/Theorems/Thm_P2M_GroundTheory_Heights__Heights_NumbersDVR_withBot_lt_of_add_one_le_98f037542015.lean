-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:50.049258+00:00
-- url     : https://prove2.me/theorems/1d271582-e0cf-4075-8129-0bcc1a094175
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one le 98f037542015: P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one le 98f037542015
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one le 98f037542015 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one le 98f037542015 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemMinimalPrimesOfDivCycleNeZero.lean#L62-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015 (x : WithBot ℕ∞) (N : ℕ)
    (hx : x + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < ((N + 1 : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«withBot_lt_of_add_one_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015
