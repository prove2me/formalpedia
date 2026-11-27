-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalMaxIdeals_proof_e44355388f30
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalMaxIdeals_proof_e44355388f30
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:16:51.58529+00:00
-- url     : https://prove2.me/theorems/43b39d2e-1559-4239-b53c-638bef68b5f9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Max Ideals proof e44355388f30: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Max Ideals proof e44355388f30
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Max Ideals proof e44355388f30 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Max Ideals proof e44355388f30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalMaxIdeals.lean#L23-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalMaxIdeals.lean#L23-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreRelDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreNonempty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocUnits
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalResidueLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalMaxIdeals
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalMaxIdeals_proof_e44355388f30 (h1 : FibreFinite.Statement.{u}) (h2 : FibreRelDim.Statement.{u})
    (h3 : FibreNonempty.Statement.{u}) (h4 : DegZeroLocUnits.Statement.{u})
    (h5 : DegZeroLocSeparate.Statement.{u}) (h6 : DegZeroLocLocalize.Statement.{u})
    (h7 : SemilocalResidueLength.Statement.{u}) : SemilocalMaxIdeals.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalMaxIdeals».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalMaxIdeals_proof_e44355388f30
