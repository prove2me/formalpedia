-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_succ_4b4521d95d09
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_succ_4b4521d95d09
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:24.241974+00:00
-- url     : https://prove2.me/theorems/584b1542-b8f4-4146-a68e-f882c1b66477
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of succ 4b4521d95d09: P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of succ 4b4521d95d09
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of succ 4b4521d95d09 construction uses the P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of succ 4b4521d95d09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookTableauCount.lean#L10-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookTableauCount
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_succ_4b4521d95d09 {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    vandermondeOf v =
      (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«vandermondeOf_succ» := P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_succ_4b4521d95d09
