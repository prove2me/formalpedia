-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:19:57.614592+00:00
-- url     : https://prove2.me/theorems/da9208d4-f81e-46d9-8e2a-684f235209a8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag z Index eq z Index iff 16e9951ee638: P2 M Ground Theory Heights  Heights Rest Terms Flag z Index eq z Index iff 16e9951ee638
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag z Index eq z Index iff 16e9951ee638 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag z Index eq z Index iff 16e9951ee638 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L166-L168

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638 (c : SmallBlock) (τ σ : Fin f) (l i : Fin a) :
    zIndex f r a c τ l = zIndex f r a c σ i ↔ τ = σ ∧ l = i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«zIndex_eq_zIndex_iff» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_zIndex_eq_zIndex_iff_16e9951ee638
