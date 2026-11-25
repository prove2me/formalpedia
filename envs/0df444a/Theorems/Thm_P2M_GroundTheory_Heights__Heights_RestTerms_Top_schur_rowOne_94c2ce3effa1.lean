-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:38.064801+00:00
-- url     : https://prove2.me/theorems/e7d43a11-3689-5a2a-a9ff-4f61bded6d7f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top schur row One 94c2ce3effa1: P2 M Ground Theory Heights  Heights Rest Terms Top schur row One 94c2ce3effa1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top schur row One 94c2ce3effa1 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top schur row One 94c2ce3effa1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLinearTermValue.lean#L45-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PLinearTermValue.lean#L45-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLinearTermValue
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1 (σ : Type*) [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 1 ≤ r) :
    schur σ (rowOne r) = ∑ i : σ, X i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«schur_rowOne» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_schur_rowOne_94c2ce3effa1
