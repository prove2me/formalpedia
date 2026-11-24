-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:18.354813+00:00
-- url     : https://prove2.me/theorems/4ff6e89a-d9f7-4515-9fb3-3f65a5d134db
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height of Point Matrix norm fe0404d8d94b: P2 M Ground Theory Heights  Heights Objects Height of Point Matrix norm fe0404d8d94b
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height of Point Matrix norm fe0404d8d94b construction uses the P2 M Ground Theory Heights  Heights Objects Height of Point Matrix norm fe0404d8d94b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L28-L31

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℂ) :
    (ofPointMatrix S hS).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«ofPointMatrix_norm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b
