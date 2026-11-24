-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:52.772848+00:00
-- url     : https://prove2.me/theorems/9964147a-0435-4d97-95ca-c057dc482b54
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height std eq of Point Matrix one d852079b1f83: P2 M Ground Theory Heights  Heights Objects Height std eq of Point Matrix one d852079b1f83
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height std eq of Point Matrix one d852079b1f83 construction uses the P2 M Ground Theory Heights  Heights Objects Height std eq of Point Matrix one d852079b1f83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L55-L56

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83 : HermNorm.std n = ofPointMatrix 1 isUnit_one := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«std_eq_ofPointMatrix_one» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_std_eq_ofPointMatrix_one_d852079b1f83
