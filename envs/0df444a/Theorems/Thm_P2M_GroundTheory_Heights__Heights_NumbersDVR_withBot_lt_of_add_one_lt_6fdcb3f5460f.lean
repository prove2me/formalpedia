-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:50.662283+00:00
-- url     : https://prove2.me/theorems/4a73016f-e8dd-42d2-a3c7-19bf5cfef029
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one lt 6fdcb3f5460f: P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one lt 6fdcb3f5460f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one lt 6fdcb3f5460f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR with Bot lt of add one lt 6fdcb3f5460f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L39-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PCutByForm.lean#L39-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«withBot_lt_of_add_one_lt» := P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_lt_6fdcb3f5460f
