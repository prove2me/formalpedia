-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:28.676942+00:00
-- url     : https://prove2.me/theorems/1e059cc1-f5a8-42d5-9a66-074f2374ad61
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum block le 1a9b559a39d2: P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum block le 1a9b559a39d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum block le 1a9b559a39d2 construction uses the P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum block le 1a9b559a39d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L18-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L18-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PPrimeLogSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open Finset
open GroundTheory.Heights₂.Heights.NineStatements.PrimeLogSum

theorem P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2 (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Nat.log 2 p = k) :
    ∑ p ∈ S, Real.log p / p ≤ 2 * Real.log 4 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«PrimeLogSum».«block_le» := P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_block_le_1a9b559a39d2
