-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:09.748511+00:00
-- url     : https://prove2.me/theorems/18d19f11-d014-48e3-9724-f7a403303b83
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur schur pad Partition 94764fcf450d: P2 M Ground Theory Heights  Heights Rest Terms Schur schur pad Partition 94764fcf450d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur schur pad Partition 94764fcf450d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur schur pad Partition 94764fcf450d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L283-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L283-L296

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable (σ : Type*) [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d {r : ℕ} (lam : Fin r → ℕ) :
    ∀ n : ℕ, r ≤ n → schur σ (padPartition n lam) = schur σ lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«schur_padPartition» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_schur_padPartition_94764fcf450d
