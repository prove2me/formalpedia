-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:17.212966+00:00
-- url     : https://prove2.me/theorems/fde8266a-eb1e-57f6-b0ee-3a26dd98fd32
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum nat Log mul log two le 171220f6ad14: P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum nat Log mul log two le 171220f6
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum nat Log mul log two le 171220f6ad14 construction uses the P2 M Ground Theory Heights  Heights Nine Statements Prime Log Sum nat Log mul log two le 171220f6ad14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PPrimeLogSum.lean#L50-L55

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

theorem P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14 {N : ℕ} (hN : N ≠ 0) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«PrimeLogSum».«natLog_mul_log_two_le» := P2M_GroundTheory_Heights__Heights_NineStatements_PrimeLogSum_natLog_mul_log_two_le_171220f6ad14
