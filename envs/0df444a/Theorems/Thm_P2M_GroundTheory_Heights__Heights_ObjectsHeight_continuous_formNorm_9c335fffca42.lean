-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:14.561345+00:00
-- url     : https://prove2.me/theorems/718691b6-a19d-4b04-815d-8b37de029c47
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height continuous form Norm 9c335fffca42: P2 M Ground Theory Heights  Heights Objects Height continuous form Norm 9c335fffca42
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height continuous form Norm 9c335fffca42 construction uses the P2 M Ground Theory Heights  Heights Objects Height continuous form Norm 9c335fffca42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L157-L161

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
variable {k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42 (S : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (IndefiniteRowSideFullHecke.ArithBezout.formNorm S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«continuous_formNorm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_formNorm_9c335fffca42
