-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:21.508279+00:00
-- url     : https://prove2.me/theorems/6ffd845d-7991-429f-81f0-5c275f2c3ebc
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measurable scale P ff4ed9e0e20e: P2 M Ground Theory Heights  Heights Log Int measurable scale P ff4ed9e0e20e
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measurable scale P ff4ed9e0e20e construction uses the P2 M Ground Theory Heights  Heights Log Int measurable scale P ff4ed9e0e20e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L87-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
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
open MeasureTheory Set MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Measurable (Function.uncurry fun θ : ℝ => scaleP p (circleMap 0 1 θ) : ℝ × (ι → ℂ) → ι → ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurable_scaleP» := P2M_GroundTheory_Heights__Heights_LogInt_measurable_scaleP_ff4ed9e0e20e
