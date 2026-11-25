-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_of_lt_of_eq_cf8434a17462
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_of_lt_of_eq_cf8434a17462
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:10.471834+00:00
-- url     : https://prove2.me/theorems/71343f40-6747-4ce1-860c-5ad2fcd98e73
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt of lt of eq cf8434a17462: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt of lt of eq cf8434a17462
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt of lt of eq cf8434a17462 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt lt of lt of eq cf8434a17462 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordInj.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordInj.lean#L9-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordInj
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_of_lt_of_eq_cf8434a17462 {m n : ℕ} (w : Fin n → Fin m) {s t : Fin n} (hst : s < t)
    (i : Fin m) (hs : w s = i) : pcnt w s i < pcnt w t i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_lt_of_lt_of_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_of_lt_of_eq_cf8434a17462
