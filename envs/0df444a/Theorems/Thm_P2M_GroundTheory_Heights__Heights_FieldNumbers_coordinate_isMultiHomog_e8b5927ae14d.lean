-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:32.876372+00:00
-- url     : https://prove2.me/theorems/154abfb6-7216-4bd8-805c-12bfffc77ac8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers coordinate is Multi Homog e8b5927ae14d: P2 M Ground Theory Heights  Heights Field Numbers coordinate is Multi Homog e8b5927ae14d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers coordinate is Multi Homog e8b5927ae14d construction uses the P2 M Ground Theory Heights  Heights Field Numbers coordinate is Multi Homog e8b5927ae14d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L142-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L142-L144

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d (N : ℕ) (i : Fin (N + 1)) :
    IsMultiHomog (X ⟨(), i⟩ : MRing (ProjIdx N) ℚ) (blockWeight (ProjIdx N) ⟨(), 0⟩) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«coordinate_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_coordinate_isMultiHomog_e8b5927ae14d
