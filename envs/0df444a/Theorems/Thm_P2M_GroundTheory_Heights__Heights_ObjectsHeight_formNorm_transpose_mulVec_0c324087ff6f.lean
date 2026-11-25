-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:17.812858+00:00
-- url     : https://prove2.me/theorems/7f75f49d-7f11-4114-8d3a-25340ae97b99
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height form Norm transpose mul Vec 0c324087ff6f: P2 M Ground Theory Heights  Heights Objects Height form Norm transpose mul Vec 0c324087ff6f
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height form Norm transpose mul Vec 0c324087ff6f construction uses the P2 M Ground Theory Heights  Heights Objects Height form Norm transpose mul Vec 0c324087ff6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L58-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L58-L62

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsUnit S) (v : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm S (Sᵀ *ᵥ v) = √(IndefiniteRowSideFullHecke.ArithBezout.normSq v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«formNorm_transpose_mulVec» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_formNorm_transpose_mulVec_0c324087ff6f
