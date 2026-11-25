-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430
-- name    : P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:57.423113+00:00
-- url     : https://prove2.me/theorems/df27e41e-3b3d-4270-97f7-8d2a51f06e65
-- title:
--   P2 M Ground Theory Heights  Heights measurable Set cone Ball 4b3833b98430: P2 M Ground Theory Heights  Heights measurable Set cone Ball 4b3833b98430
-- statement:
--   The P2 M Ground Theory Heights  Heights measurable Set cone Ball 4b3833b98430 construction uses the P2 M Ground Theory Heights  Heights measurable Set cone Ball 4b3833b98430 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeLogBound.lean#L56-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
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
open MvPolynomial MeasureTheory NumberField Matrix
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430 (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«measurableSet_coneBall» := P2M_GroundTheory_Heights__Heights_measurableSet_coneBall_4b3833b98430
