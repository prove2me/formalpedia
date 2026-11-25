-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartX_C_e13c0da01265
-- name    : P2M_GroundTheory_Heights__Heights_chartX_C_e13c0da01265
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:54.737941+00:00
-- url     : https://prove2.me/theorems/d8352920-d494-4744-a86f-fea01785783b
-- title:
--   P2 M Ground Theory Heights  Heights chart X C e13c0da01265: P2 M Ground Theory Heights  Heights chart X C e13c0da01265
-- statement:
--   The P2 M Ground Theory Heights  Heights chart X C e13c0da01265 construction uses the P2 M Ground Theory Heights  Heights chart X C e13c0da01265 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_chartX_C_e13c0da01265 (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartX_C» := P2M_GroundTheory_Heights__Heights_chartX_C_e13c0da01265
