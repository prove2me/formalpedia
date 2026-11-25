-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:29.581481+00:00
-- url     : https://prove2.me/theorems/c3718b75-08b0-4149-b703-df7374fc0eee
-- title:
--   P2 M Ground Theory Heights  Heights Log Int is Weighted Homogeneous component of c4f8385f16e7: P2 M Ground Theory Heights  Heights Log Int is Weighted Homogeneous component of c4f8385f16e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int is Weighted Homogeneous component of c4f8385f16e7 construction uses the P2 M Ground Theory Heights  Heights Log Int is Weighted Homogeneous component of c4f8385f16e7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L196-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntPoly.lean#L196-L203

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

theorem P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7 (w w' : ι → ℕ) (g : MvPolynomial ι ℂ) (d e : ℕ)
    (h : IsWeightedHomogeneous w g e) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w' d g) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«isWeightedHomogeneous_component_of» := P2M_GroundTheory_Heights__Heights_LogInt_isWeightedHomogeneous_component_of_c4f8385f16e7
