-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalIntegralClosureFinite_proof_0a2405da4010
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalIntegralClosureFinite_proof_0a2405da4010
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:14:31.599208+00:00
-- url     : https://prove2.me/theorems/c1396437-72a0-4735-92c3-e9f29ba21cf5
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Local Integral Closure Finite proof 0a2405da4010: P2 M Ground Theory Heights  Heights Field Numbers Local Integral Closure Finite proof 0a2405da4010
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Local Integral Closure Finite proof 0a2405da4010 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Local Integral Closure Finite proof 0a2405da4010 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PLocalIntegralClosureFinite.lean#L19-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PLocalIntegralClosureFinite.lean#L19-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PLocalIntegralClosureFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalIntegralClosureFinite_proof_0a2405da4010 (hN : NoetherIntegralClosureFinite.Statement.{u})
    (hF : FunctionFieldFinite.Statement.{u}) (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (hFr : DegZeroLocFrac.Statement.{u}) :
    LocalIntegralClosureFinite.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«LocalIntegralClosureFinite».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalIntegralClosureFinite_proof_0a2405da4010
