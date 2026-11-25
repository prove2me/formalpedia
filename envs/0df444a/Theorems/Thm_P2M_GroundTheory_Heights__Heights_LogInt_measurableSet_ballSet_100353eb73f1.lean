-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_ballSet_100353eb73f1
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_ballSet_100353eb73f1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:34.475981+00:00
-- url     : https://prove2.me/theorems/a96863e0-f665-5595-9498-6ba7e43fb1fc
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measurable Set ball Set 100353eb73f1: P2 M Ground Theory Heights  Heights Log Int measurable Set ball Set 100353eb73f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measurable Set ball Set 100353eb73f1 construction uses the P2 M Ground Theory Heights  Heights Log Int measurable Set ball Set 100353eb73f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/MahlerMul.lean#L19-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
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
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_ballSet_100353eb73f1 (h : HermNorm n) : MeasurableSet (ballSet h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurableSet_ballSet» := P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_ballSet_100353eb73f1
