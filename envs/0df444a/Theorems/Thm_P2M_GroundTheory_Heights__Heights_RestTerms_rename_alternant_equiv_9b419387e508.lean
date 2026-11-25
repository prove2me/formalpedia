-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rename_alternant_equiv_9b419387e508
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rename_alternant_equiv_9b419387e508
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:52.526323+00:00
-- url     : https://prove2.me/theorems/e1d3a564-4dd8-572e-963b-a903358e8d0d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms rename alternant equiv 9b419387e508: P2 M Ground Theory Heights  Heights Rest Terms rename alternant equiv 9b419387e508
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms rename alternant equiv 9b419387e508 construction uses the P2 M Ground Theory Heights  Heights Rest Terms rename alternant equiv 9b419387e508 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAlternantRenamePlace.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAlternantRenamePlace.lean#L12-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAlternantRenamePlace
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rename_alternant_equiv_9b419387e508 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (v : ι → ℕ) :
    rename e (alternant v) = alternant (v ∘ e.symm) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rename_alternant_equiv» := P2M_GroundTheory_Heights__Heights_RestTerms_rename_alternant_equiv_9b419387e508
