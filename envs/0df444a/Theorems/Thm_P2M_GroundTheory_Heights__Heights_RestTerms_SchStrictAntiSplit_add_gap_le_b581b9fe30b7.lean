-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:53.207657+00:00
-- url     : https://prove2.me/theorems/feac6ae4-f966-4256-9ea0-3450aa0ee2a6
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split add gap le b581b9fe30b7: P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split add gap le b581b9fe30b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split add gap le b581b9fe30b7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split add gap le b581b9fe30b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchStrictAntiSplit.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchStrictAntiSplit.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchStrictAntiSplit
import Theorems.Thm_UpperTheory_Reformulated_B_Yoa4_add_gap_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7 {r : ℕ} {d : Fin r → ℕ} (hd : StrictAnti d) :
    ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k → d j + k ≤ d i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchStrictAntiSplit».«add_gap_le» := P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_add_gap_le_b581b9fe30b7
