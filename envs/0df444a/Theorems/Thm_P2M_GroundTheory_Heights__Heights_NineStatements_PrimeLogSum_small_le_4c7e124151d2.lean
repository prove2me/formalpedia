-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:22.533151+00:00
-- url     : https://prove2.me/theorems/d0feb9cb-3459-590e-8249-3d6bd4ad86f4
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum small le 4c7e124151d2: P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum small le 4c7e124151d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum small le 4c7e124151d2 construction uses the P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum small le 4c7e124151d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L57-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L57-L88

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2 {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    ∑ p ∈ S, Real.log p / p ≤ 8 * Real.log N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«PrimeLogSum».«small_le» := P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_small_le_4c7e124151d2
