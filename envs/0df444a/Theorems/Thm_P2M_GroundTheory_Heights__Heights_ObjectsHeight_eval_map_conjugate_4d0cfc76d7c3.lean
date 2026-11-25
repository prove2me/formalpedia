-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:12:57.455666+00:00
-- url     : https://prove2.me/theorems/86769cdd-6b89-417d-9c6b-388f1aa84bdc
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height eval map conjugate 4d0cfc76d7c3: P2 M Ground Theory Heights  Heights Objects Height eval map conjugate 4d0cfc76d7c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height eval map conjugate 4d0cfc76d7c3 construction uses the P2 M Ground Theory Heights  Heights Objects Height eval map conjugate 4d0cfc76d7c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L414-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L414-L421

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3 {K : Type*} [Field K] {ι : Type*} (σ : K →+* ℂ)
    (f : MvPolynomial ι K) (x : ι → ℂ) :
    eval x (f.map (ComplexEmbedding.conjugate σ)) =
      starRingEnd ℂ (eval (star x) (f.map σ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«eval_map_conjugate» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3
