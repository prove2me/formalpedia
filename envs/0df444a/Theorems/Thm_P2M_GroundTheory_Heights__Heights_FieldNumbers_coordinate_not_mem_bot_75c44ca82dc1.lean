-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:12.203958+00:00
-- url     : https://prove2.me/theorems/cac35c35-489d-40a0-8b82-5c4016b89a30
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coordinate not mem bot 75c44ca82dc1: P2 M Ground Theory Heights  Heights Field Numbers coordinate not mem bot 75c44ca82dc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coordinate not mem bot 75c44ca82dc1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers coordinate not mem bot 75c44ca82dc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L146-L149

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1 (N : ℕ) (i : Fin (N + 1)) :
    (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) ∉ (⊥ : Ideal (MRing (ProjIdx N) ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coordinate_not_mem_bot» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_not_mem_bot_75c44ca82dc1
