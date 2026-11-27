-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalLength_proof_35f32fadaed3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalLength_proof_35f32fadaed3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:31.879483+00:00
-- url     : https://prove2.me/theorems/5f8b49b6-1301-427d-80f1-6232da1499f1
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cone Local Length proof 35f32fadaed3: P2 M Ground Theory Heights  Heights Field Numbers Cone Local Length proof 35f32fadaed3
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cone Local Length proof 35f32fadaed3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cone Local Length proof 35f32fadaed3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PConeLocalLength.lean#L17-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PConeLocalLength.lean#L17-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalizedQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConeLocalLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing
noncomputable section
universe u
set_option maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalLength_proof_35f32fadaed3 (h₁ : LocalizedQuotientLength.Statement.{u, u})
    (h₂ : ConeLocalFlat.Statement.{u}) : ConeLocalLength.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ConeLocalLength».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeLocalLength_proof_35f32fadaed3
