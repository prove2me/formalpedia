-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:11.40109+00:00
-- url     : https://prove2.me/theorems/97aca77e-b346-49d8-b2bd-44b9a6e9e165
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height cond smul f954aab74cd5: P2 M Ground Theory Heights  Heights Objects Height cond smul f954aab74cd5
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height cond smul f954aab74cd5 construction uses the P2 M Ground Theory Heights  Heights Objects Height cond smul f954aab74cd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L69-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5 {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    {c : ENNReal} (h0 : c ≠ 0) (htop : c ≠ ⊤) : cond (c • μ) s = cond μ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«cond_smul» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_smul_f954aab74cd5
