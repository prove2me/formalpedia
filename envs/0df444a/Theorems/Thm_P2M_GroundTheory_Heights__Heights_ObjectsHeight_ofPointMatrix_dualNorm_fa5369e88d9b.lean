-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:23.037162+00:00
-- url     : https://prove2.me/theorems/1fc9127e-5f62-443f-b22e-a26cea66b01e
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height of Point Matrix dual Norm fa5369e88d9b: P2 M Ground Theory Heights  Heights Objects Height of Point Matrix dual Norm fa5369e88d9b
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height of Point Matrix dual Norm fa5369e88d9b construction uses the P2 M Ground Theory Heights  Heights Objects Height of Point Matrix dual Norm fa5369e88d9b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L33-L38

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (y : Fin n → ℂ) :
    (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«ofPointMatrix_dualNorm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b
