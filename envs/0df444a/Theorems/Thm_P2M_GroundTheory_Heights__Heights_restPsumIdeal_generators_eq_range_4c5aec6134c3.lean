-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3
-- name    : P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:30.452869+00:00
-- url     : https://prove2.me/theorems/70064312-ece4-5293-97ab-74135157ddb3
-- title:
--   P2 M Ground Theory Heights  Heights rest Psum Ideal generators eq range 4c5aec6134c3: P2 M Ground Theory Heights  Heights rest Psum Ideal generators eq range 4c5aec6134c3
-- statement:
--   The P2 M Ground Theory Heights  Heights rest Psum Ideal generators eq range 4c5aec6134c3 construction uses the P2 M Ground Theory Heights  Heights rest Psum Ideal generators eq range 4c5aec6134c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIdealSum.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutIdealSum.lean#L9-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutIdealSum
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
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3 (f N : ℕ) :
    {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = RestTerms.blockPowerSum f N k τ} =
      Set.range fun i : Fin N × Fin f => RestTerms.blockPowerSum f N ((i.1 : ℕ) + 1) i.2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«restPsumIdeal_generators_eq_range» := P2M_GroundTheory_Heights__Heights_restPsumIdeal_generators_eq_range_4c5aec6134c3
