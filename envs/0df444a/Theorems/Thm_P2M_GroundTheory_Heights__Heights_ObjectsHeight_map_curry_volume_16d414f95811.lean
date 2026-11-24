-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:18.783606+00:00
-- url     : https://prove2.me/theorems/6cf2a5f9-3c08-463e-b3f8-3970fa2d6da7
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height map curry volume 16d414f95811: P2 M Ground Theory Heights  Heights Objects Height map curry volume 16d414f95811
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height map curry volume 16d414f95811 construction uses the P2 M Ground Theory Heights  Heights Objects Height map curry volume 16d414f95811 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L81-L94

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811 :
    (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) =
      Measure.pi fun _ : Fin k => (volume : Measure (Fin n → ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«map_curry_volume» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_map_curry_volume_16d414f95811
