-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:53.885468+00:00
-- url     : https://prove2.me/theorems/45651c94-38ad-5de6-bc8c-a846afe7061e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Semilocal Finite Rank proof 9f2f42e18824: P2 M Ground Theory Heights  Heights Field Numbers Semilocal Finite Rank proof 9f2f42e18824
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Semilocal Finite Rank proof 9f2f42e18824 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Semilocal Finite Rank proof 9f2f42e18824 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L63-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L63-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824 (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«SemilocalFiniteRank».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824
