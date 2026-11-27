-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ConePolyLocalization_proof_a31237763a2c
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ConePolyLocalization_proof_a31237763a2c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:11:56.031091+00:00
-- url     : https://prove2.me/theorems/9455ea85-00bd-5e67-97f3-fcbf6609868b
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Cone Poly Localization proof a31237763a2c: P2 M Ground Theory Heights  Heights Field Numbers Cone Poly Localization proof a31237763a2c
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Cone Poly Localization proof a31237763a2c construction uses the P2 M Ground Theory Heights  Heights Field Numbers Cone Poly Localization proof a31237763a2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PConePolyLocalization.lean#L18-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PConePolyLocalization.lean#L18-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarSurj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConePolyLocalization
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ConePolyLocalization_proof_a31237763a2c (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ConePolyLocalization».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ConePolyLocalization_proof_a31237763a2c
