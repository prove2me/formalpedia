-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalResidueLength_proof_25f72b584279
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalResidueLength_proof_25f72b584279
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:47.574928+00:00
-- url     : https://prove2.me/theorems/223f6fd6-5b68-5e60-999b-284d9d9c294f
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Residue Length proof 25f72b584279: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Residue Length proof 25f72b584279
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Residue Length proof 25f72b584279 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Residue Length proof 25f72b584279 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalResidueLength.lean#L21-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalResidueLength.lean#L21-L109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalResidueLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalResidueLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_proof_46b509c2b5c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FibreFinite_proof_e5ac3cafe5ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_proof_c7e248874611
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
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalResidueLength_proof_25f72b584279 (hRes : DegZeroLocResidue.Statement.{u})
    (hFR : SemilocalFiniteRank.Statement.{u}) (hLoc : DegZeroLocLocalize.Statement.{u}) :
    SemilocalResidueLength.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalResidueLength».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalResidueLength_proof_25f72b584279
