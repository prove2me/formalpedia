-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:33.224344+00:00
-- url     : https://prove2.me/theorems/22655c54-ea4a-4878-bc11-a939dd595577
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur rename complete Symmetric 4ab9f77ac719: P2 M Ground Theory Heights  Heights Rest Terms Schur rename complete Symmetric 4ab9f77ac719
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur rename complete Symmetric 4ab9f77ac719 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur rename complete Symmetric 4ab9f77ac719 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L304-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L304-L309

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719 (e : Equiv.Perm σ) (d : ℤ) :
    rename e (completeSymmetric σ d) = completeSymmetric σ d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«rename_completeSymmetric» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_rename_completeSymmetric_4ab9f77ac719
