-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_proof_50f5ecdcc75d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_proof_50f5ecdcc75d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:30.848096+00:00
-- url     : https://prove2.me/theorems/2d5a210a-d1a0-43b4-a325-f22977b94da1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num proof 50f5ecdcc75d: P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num proof 50f5ecdcc75d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num proof 50f5ecdcc75d construction uses the P2 M Ground Theory Heights  Heights Field Numbers Rename Int Num proof 50f5ecdcc75d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameIntNum.lean#L62-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_proof_50f5ecdcc75d (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«RenameIntNum».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_proof_50f5ecdcc75d
