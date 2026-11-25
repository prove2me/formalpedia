-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:14:13.471808+00:00
-- url     : https://prove2.me/theorems/58eeb2e0-943d-4250-a020-2feaea0a141f
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height continuous herm Norm 490b6c9ab1d6: P2 M Ground Theory Heights  Heights Objects Height continuous herm Norm 490b6c9ab1d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height continuous herm Norm 490b6c9ab1d6 construction uses the P2 M Ground Theory Heights  Heights Objects Height continuous herm Norm 490b6c9ab1d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L391-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L391-L395

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6 (h : HermNorm n) : Continuous h.norm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«continuous_hermNorm» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_continuous_hermNorm_490b6c9ab1d6
