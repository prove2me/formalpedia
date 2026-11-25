-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:56.76482+00:00
-- url     : https://prove2.me/theorems/6c189a38-d2bf-446f-ab4f-bfa33c85f9fc
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag card filter pair 8f784f72c70f: P2 M Ground Theory Heights  Heights Rest Terms Flag card filter pair 8f784f72c70f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag card filter pair 8f784f72c70f construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag card filter pair 8f784f72c70f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L285-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L285-L300

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f {f N : ℕ} (s : Finset (Fin N)) (τ : Fin f) (v : Fin f × Fin N) :
    (s.filter fun i => ((τ, i) : Fin f × Fin N) = v).card = if v.1 = τ ∧ v.2 ∈ s then 1 else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«card_filter_pair» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_card_filter_pair_8f784f72c70f
