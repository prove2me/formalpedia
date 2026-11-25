-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_normSq_f96758e0920b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_normSq_f96758e0920b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:05.750276+00:00
-- url     : https://prove2.me/theorems/136b8722-a97a-4b3a-8ad8-a029cab3761a
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height continuous norm Sq f96758e0920b: P2 M Ground Theory Heights  Heights Objects Height continuous norm Sq f96758e0920b
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height continuous norm Sq f96758e0920b construction uses the P2 M Ground Theory Heights  Heights Objects Height continuous norm Sq f96758e0920b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L163-L165

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_normSq_f96758e0920b : Continuous (IndefiniteRowSideFullHecke.ArithBezout.normSq (n := n)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«continuous_normSq» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_normSq_f96758e0920b
