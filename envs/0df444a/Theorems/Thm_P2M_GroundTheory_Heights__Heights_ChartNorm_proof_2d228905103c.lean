-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNorm_proof_2d228905103c
-- name    : P2M_GroundTheory_Heights__Heights_ChartNorm_proof_2d228905103c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:08:52.661359+00:00
-- url     : https://prove2.me/theorems/58d49843-68bb-5445-a85e-856be83417dd
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm proof 2d228905103c: P2 M Ground Theory Heights  Heights Chart Norm proof 2d228905103c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm proof 2d228905103c construction uses the P2 M Ground Theory Heights  Heights Chart Norm proof 2d228905103c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L128-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean#L128-L170

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

theorem P2M_GroundTheory_Heights__Heights_ChartNorm_proof_2d228905103c (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedForm.Statement) : ChartNorm.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNorm».«proof» := P2M_GroundTheory_Heights__Heights_ChartNorm_proof_2d228905103c
