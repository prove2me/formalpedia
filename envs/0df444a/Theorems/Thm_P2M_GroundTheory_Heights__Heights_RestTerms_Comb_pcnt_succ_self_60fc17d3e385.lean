-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:04:58.941305+00:00
-- url     : https://prove2.me/theorems/55ccf2a7-9ac0-571e-a1a1-17da60cee30f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt succ self 60fc17d3e385: P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt succ self 60fc17d3e385
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt succ self 60fc17d3e385 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Comb pcnt succ self 60fc17d3e385 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordMono.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombCellOfWordMono.lean#L10-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordMono
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385 {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w ((t : ℕ) + 1) (w t) = pcnt w t (w t) + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Comb».«pcnt_succ_self» := P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_succ_self_60fc17d3e385
