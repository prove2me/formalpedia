-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalLengthSum_proof_0000ece1d41e
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalLengthSum_proof_0000ece1d41e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:21.977148+00:00
-- url     : https://prove2.me/theorems/d48ff0b5-9b16-4b7d-b446-9ebed4674e27
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Length Sum proof 0000ece1d41e: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Length Sum proof 0000ece1d41e
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Length Sum proof 0000ece1d41e construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Length Sum proof 0000ece1d41e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalLengthSum.lean#L18-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalLengthSum.lean#L18-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFiniteAlgebraLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalLengthSum
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalLengthSum_proof_0000ece1d41e (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalLengthSum».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalLengthSum_proof_0000ece1d41e
