-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:41.675635+00:00
-- url     : https://prove2.me/theorems/c810a312-1d44-4e70-961d-5222a1460bc7
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height euclid norm eq 471a80e339c7: P2 M Ground Theory Heights  Heights Objects Height euclid norm eq 471a80e339c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height euclid norm eq 471a80e339c7 construction uses the P2 M Ground Theory Heights  Heights Objects Height euclid norm eq 471a80e339c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L16-L17

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7 (v : Fin n → ℂ) : ‖WithLp.toLp 2 v‖ = √(∑ i, ‖v i‖ ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«euclid_norm_eq» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7
