-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_pcnt_of_eq_2f99943eebf6
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_pcnt_of_eq_2f99943eebf6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:04:45.007457+00:00
-- url     : https://prove2.me/theorems/05e13d23-8f91-5bd0-b238-ff00092b5858
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt pcnt of eq 2f99943eebf6: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt pcnt of eq 2f99943eebf6
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt pcnt of eq 2f99943eebf6 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt pcnt of eq 2f99943eebf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordMem.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordMem.lean#L9-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordMem
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
open Finset Comb

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_pcnt_of_eq_2f99943eebf6 {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w t (w t) < pcnt w n (w t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_lt_pcnt_of_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_pcnt_of_eq_2f99943eebf6
