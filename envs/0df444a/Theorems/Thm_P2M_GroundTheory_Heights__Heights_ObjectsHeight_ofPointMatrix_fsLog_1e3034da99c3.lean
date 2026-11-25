-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:07.353856+00:00
-- url     : https://prove2.me/theorems/4103ec12-6ff5-4f57-aee3-e2540432268d
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height of Point Matrix fs Log 1e3034da99c3: P2 M Ground Theory Heights  Heights Objects Height of Point Matrix fs Log 1e3034da99c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height of Point Matrix fs Log 1e3034da99c3 construction uses the P2 M Ground Theory Heights  Heights Objects Height of Point Matrix fs Log 1e3034da99c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L40-L44

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3 (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u y : Fin n → ℂ) :
    fsLog (ofPointMatrix S hS) u y =
      IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u (fun p => y p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«ofPointMatrix_fsLog» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_fsLog_1e3034da99c3
