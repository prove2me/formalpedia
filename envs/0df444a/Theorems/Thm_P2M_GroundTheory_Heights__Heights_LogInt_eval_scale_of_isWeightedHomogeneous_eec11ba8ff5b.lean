-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:02.254711+00:00
-- url     : https://prove2.me/theorems/2fbf016e-d5b3-444f-aec9-d85e33caff00
-- title:
--   P2 M Ground Theory Heights  Heights Log Int eval scale of is Weighted Homogeneous eec11ba8ff5b: P2 M Ground Theory Heights  Heights Log Int eval scale of is Weighted Homogeneous eec11ba8ff5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int eval scale of is Weighted Homogeneous eec11ba8ff5b construction uses the P2 M Ground Theory Heights  Heights Log Int eval scale of is Weighted Homogeneous eec11ba8ff5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L127-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b {ι : Type*} (p : ι → Prop) [DecidablePred p] (a : ℂ) (v : ι → ℂ)
    (g : MvPolynomial ι ℂ) (d : ℕ) (hg : IsWeightedHomogeneous (indW p) g d) :
    eval (scaleP p a v) g = a ^ d * eval v g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«eval_scale_of_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_LogInt_eval_scale_of_isWeightedHomogeneous_eec11ba8ff5b
