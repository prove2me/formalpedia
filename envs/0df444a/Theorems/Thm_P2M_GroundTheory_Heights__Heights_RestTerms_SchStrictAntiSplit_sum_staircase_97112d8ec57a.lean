-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:21:15.893801+00:00
-- url     : https://prove2.me/theorems/660ebf39-0133-44ba-b75d-49661875172d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split sum staircase 97112d8ec57a: P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split sum staircase 97112d8ec57a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split sum staircase 97112d8ec57a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Strict Anti Split sum staircase 97112d8ec57a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchStrictAntiSplit.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchStrictAntiSplit.lean#L15-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AddGapLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchStrictAntiSplit
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchStrictAntiSplit».«sum_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_SchStrictAntiSplit_sum_staircase_97112d8ec57a
