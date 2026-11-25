-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:03.066784+00:00
-- url     : https://prove2.me/theorems/97e3ef1b-ec85-5529-82fc-cf2ba9b9364d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag y Index eq y Index iff 2a9541f0912b: P2 M Ground Theory Heights  Heights Rest Terms Flag y Index eq y Index iff 2a9541f0912b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag y Index eq y Index iff 2a9541f0912b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag y Index eq y Index iff 2a9541f0912b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L162-L164

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable {f r a : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b (c : SmallBlock) (τ σ : Fin f) (l i : Fin r) :
    yIndex f r a c τ l = yIndex f r a c σ i ↔ τ = σ ∧ l = i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«yIndex_eq_yIndex_iff» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_eq_yIndex_iff_2a9541f0912b
