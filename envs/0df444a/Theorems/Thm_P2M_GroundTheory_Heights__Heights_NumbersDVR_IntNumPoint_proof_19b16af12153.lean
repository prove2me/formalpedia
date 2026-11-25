-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:36.876558+00:00
-- url     : https://prove2.me/theorems/888b0140-e9c6-4aba-b4d5-d13cda2afc2b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point proof 19b16af12153: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point proof 19b16af12153
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point proof 19b16af12153 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point proof 19b16af12153 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L219-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L219-L227

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153 (hBase : FieldNumbers.IntNumBase.Statement.{u}) : IntNumPoint.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153
