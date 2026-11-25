-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:09.504531+00:00
-- url     : https://prove2.me/theorems/1e0601f2-ebda-447b-b33c-f906c087b6cb
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height volume norm Sq eq one e3f936075ac2: P2 M Ground Theory Heights  Heights Objects Height volume norm Sq eq one e3f936075ac2
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height volume norm Sq eq one e3f936075ac2 construction uses the P2 M Ground Theory Heights  Heights Objects Height volume norm Sq eq one e3f936075ac2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L96-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L96-L116

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2 :
    (volume : Measure (Fin n → ℂ)) {v | IndefiniteRowSideFullHecke.ArithBezout.normSq v = 1} = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«volume_normSq_eq_one» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_volume_normSq_eq_one_e3f936075ac2
