-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:52.106287+00:00
-- url     : https://prove2.me/theorems/edc5bf20-3dbd-4df6-bb5e-b562028abf67
-- title:
--   P2 M Ground Theory Heights  Heights Log Int norm scale P circle Map 6234e06e9fbd: P2 M Ground Theory Heights  Heights Log Int norm scale P circle Map 6234e06e9fbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int norm scale P circle Map 6234e06e9fbd construction uses the P2 M Ground Theory Heights  Heights Log Int norm scale P circle Map 6234e06e9fbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L97-L99

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd (p : ι → Prop) [DecidablePred p] (θ : ℝ) (u : ι → ℂ) (x : ι) :
    ‖scaleP p (circleMap 0 1 θ) u x‖ = ‖u x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«norm_scaleP_circleMap» := P2M_GroundTheory_Heights__Heights_LogInt_norm_scaleP_circleMap_6234e06e9fbd
