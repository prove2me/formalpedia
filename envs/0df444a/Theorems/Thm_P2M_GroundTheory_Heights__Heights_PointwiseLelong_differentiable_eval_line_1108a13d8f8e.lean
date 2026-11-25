-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:20.4568+00:00
-- url     : https://prove2.me/theorems/b0f07531-c210-4543-ae9c-2f2c846b5fd4
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong differentiable eval line 1108a13d8f8e: P2 M Ground Theory Heights  Heights Pointwise Lelong differentiable eval line 1108a13d8f8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong differentiable eval line 1108a13d8f8e construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong differentiable eval line 1108a13d8f8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L27-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e (Q : MvPolynomial (Fin N) ℂ) (v u : Fin N → ℂ) :
    Differentiable ℂ fun w : ℂ => eval (v + w • u) Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«differentiable_eval_line» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_differentiable_eval_line_1108a13d8f8e
