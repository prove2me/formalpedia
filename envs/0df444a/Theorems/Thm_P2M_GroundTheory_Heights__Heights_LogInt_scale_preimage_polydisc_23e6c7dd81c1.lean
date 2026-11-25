-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:21.328353+00:00
-- url     : https://prove2.me/theorems/f4f26a09-0567-459d-982d-36c78c1ca442
-- title:
--   P2 M Ground Theory Heights  Heights Log Int scale preimage polydisc 23e6c7dd81c1: P2 M Ground Theory Heights  Heights Log Int scale preimage polydisc 23e6c7dd81c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int scale preimage polydisc 23e6c7dd81c1 construction uses the P2 M Ground Theory Heights  Heights Log Int scale preimage polydisc 23e6c7dd81c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L101-L104

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1 (p : ι → Prop) [DecidablePred p] (θ : ℝ) (r : ℝ) :
    scaleP p (circleMap 0 1 θ) ⁻¹' polydisc ι r = polydisc ι r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«scale_preimage_polydisc» := P2M_GroundTheory_Heights__Heights_LogInt_scale_preimage_polydisc_23e6c7dd81c1
