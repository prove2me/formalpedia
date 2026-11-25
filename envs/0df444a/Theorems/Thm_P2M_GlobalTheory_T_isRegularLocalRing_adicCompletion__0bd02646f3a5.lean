-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5
-- name    : P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:30.39135+00:00
-- url     : https://prove2.me/theorems/d6f89461-89f8-45f2-9963-3f66b4878397
-- title:
--   P2 M Global Theory T is Regular Local Ring adic Completion  0bd02646f3a5: P2 M Global Theory T is Regular Local Ring adic Completion  0bd02646f3a5
-- statement:
--   The P2 M Global Theory T is Regular Local Ring adic Completion  0bd02646f3a5 construction uses the P2 M Global Theory T is Regular Local Ring adic Completion  0bd02646f3a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsRegularLocalRingAdicCompletionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsRegularLocalRingAdicCompletionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5 : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by sorry

alias «GlobalTheory».«T».«isRegularLocalRing_adicCompletion'» := P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5
