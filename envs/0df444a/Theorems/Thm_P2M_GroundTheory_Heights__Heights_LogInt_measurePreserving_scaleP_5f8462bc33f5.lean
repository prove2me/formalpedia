-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:19.490769+00:00
-- url     : https://prove2.me/theorems/a0cf690c-705e-481c-875f-9ad47890e490
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measure Preserving scale P 5f8462bc33f5: P2 M Ground Theory Heights  Heights Log Int measure Preserving scale P 5f8462bc33f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measure Preserving scale P 5f8462bc33f5 construction uses the P2 M Ground Theory Heights  Heights Log Int measure Preserving scale P 5f8462bc33f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L72-L85

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5 [Fintype ι] (p : ι → Prop) [DecidablePred p] (θ : ℝ) :
    MeasurePreserving (scaleP p (circleMap 0 1 θ)) volume volume := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurePreserving_scaleP» := P2M_GroundTheory_Heights__Heights_LogInt_measurePreserving_scaleP_5f8462bc33f5
