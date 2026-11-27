-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_proof_feadc2837ee9
-- name    : P2M_GroundTheory_Heights__Heights_SectionNorm_proof_feadc2837ee9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:38:31.086338+00:00
-- url     : https://prove2.me/theorems/8b0d3772-984f-5adc-a935-aa5ccee71b15
-- title:
--   P2 M Ground Theory Heights  Heights Section Norm proof feadc2837ee9: P2 M Ground Theory Heights  Heights Section Norm proof feadc2837ee9
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Norm proof feadc2837ee9 construction uses the P2 M Ground Theory Heights  Heights Section Norm proof feadc2837ee9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L58-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomial.lean#L58-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionNorm_proof_feadc2837ee9 (hP : ConePoints.Statement) (hM : ChartMetric.Statement) :
    SectionNorm.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionNorm».«proof» := P2M_GroundTheory_Heights__Heights_SectionNorm_proof_feadc2837ee9
