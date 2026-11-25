-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:34.879296+00:00
-- url     : https://prove2.me/theorems/7f0dde9d-a9b0-4bb4-b641-61f3dcf0ef0d
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum large le 8775b716dccb: P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum large le 8775b716dccb
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum large le 8775b716dccb construction uses the P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum large le 8775b716dccb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L90-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L90-L123

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ) (hS : ∀ p ∈ S, B < p) (hcard : S.card ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«PrimeLogSum».«large_le» := P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_large_le_8775b716dccb
