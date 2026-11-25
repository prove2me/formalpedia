-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:02.065274+00:00
-- url     : https://prove2.me/theorems/57c7bb24-a8c8-59f9-95bf-2b2f9eadd343
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms card lattice Words zero of eq zero ae88b6fd3ba2: P2 M Ground Theory Heights  Heights Rest Terms card lattice Words zero of eq zero ae88b6fd3ba2
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms card lattice Words zero of eq zero ae88b6fd3ba2 construction uses the P2 M Ground Theory Heights  Heights Rest Terms card lattice Words zero of eq zero ae88b6fd3ba2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombHookCount.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCombHookCount.lean#L11-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookCount
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2 {r : ℕ} (lam : Fin r → ℕ) (hlam : ∀ i, lam i = 0) :
    (latticeWords 0 lam).card = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«card_latticeWords_zero_of_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_card_latticeWords_zero_of_eq_zero_ae88b6fd3ba2
