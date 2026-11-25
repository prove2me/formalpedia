-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:59.15281+00:00
-- url     : https://prove2.me/theorems/1bd1550d-42da-4438-8e34-2a055cb5777d
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measure Preserving mul circle Map a47a1e5d7020: P2 M Ground Theory Heights  Heights Log Int measure Preserving mul circle Map a47a1e5d7020
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measure Preserving mul circle Map a47a1e5d7020 construction uses the P2 M Ground Theory Heights  Heights Log Int measure Preserving mul circle Map a47a1e5d7020 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L63-L70

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020 (θ : ℝ) :
    MeasurePreserving (fun z : ℂ => circleMap 0 1 θ * z) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurePreserving_mul_circleMap» := P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_mul_circleMap_a47a1e5d7020
