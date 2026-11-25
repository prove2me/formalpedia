-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartHomog_proof_29d23d70cc5a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartHomog_proof_29d23d70cc5a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:04:38.529403+00:00
-- url     : https://prove2.me/theorems/9ebd4cf9-8fec-5cb3-97cf-92dcb8960630
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers MChart Homog proof 29d23d70cc5a: P2 M Ground Theory Heights  Heights Field Numbers MChart Homog proof 29d23d70cc5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers MChart Homog proof 29d23d70cc5a construction uses the P2 M Ground Theory Heights  Heights Field Numbers MChart Homog proof 29d23d70cc5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L65-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMChartHomog.lean#L65-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartHomog_proof_29d23d70cc5a : MChartHomog.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MChartHomog».«proof» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartHomog_proof_29d23d70cc5a
