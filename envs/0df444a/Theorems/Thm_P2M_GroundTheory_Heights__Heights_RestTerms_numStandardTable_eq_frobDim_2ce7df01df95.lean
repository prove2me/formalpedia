-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:10.170528+00:00
-- url     : https://prove2.me/theorems/3adfed3b-619f-4b84-af59-89b128f34572
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms num Standard Table eq frob Dim 2ce7df01df95: P2 M Ground Theory Heights  Heights Rest Terms num Standard Table eq frob Dim 2ce7df01df95
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms num Standard Table eq frob Dim 2ce7df01df95 construction uses the P2 M Ground Theory Heights  Heights Rest Terms num Standard Table eq frob Dim 2ce7df01df95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLemmaC.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLemmaC.lean#L10-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaC
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95 (h1 : FrobeniusDimensionFormula.Statement) {m : ℕ}
    (lam : Fin m → ℕ) (hlam : Antitone lam) :
    (numStandardTable lam : ℚ) = GroundTheory.Heights₂.Heights.frobDim lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«numStandardTable_eq_frobDim» := P2M_GroundTheory_Heights__Heights_RestTerms_numStandardTable_eq_frobDim_2ce7df01df95
