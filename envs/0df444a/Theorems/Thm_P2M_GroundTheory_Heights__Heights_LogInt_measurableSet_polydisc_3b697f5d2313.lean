-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:53.205976+00:00
-- url     : https://prove2.me/theorems/e2650111-107a-4e2b-8013-df39a5b3f180
-- title:
--   P2 M Ground Theory Heights  Heights Log Int measurable Set polydisc 3b697f5d2313: P2 M Ground Theory Heights  Heights Log Int measurable Set polydisc 3b697f5d2313
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int measurable Set polydisc 3b697f5d2313 construction uses the P2 M Ground Theory Heights  Heights Log Int measurable Set polydisc 3b697f5d2313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L106-L107

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313 [Fintype ι] (r : ℝ) : MeasurableSet (polydisc ι r) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«measurableSet_polydisc» := P2M_GroundTheory_Heights__Heights_LogInt_measurableSet_polydisc_3b697f5d2313
