-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:39:28.880542+00:00
-- url     : https://prove2.me/theorems/1826d795-46be-5558-93de-c00b214e3565
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At poly R 1a5b2ce114a0: P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At poly R 1a5b2ce114a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At poly R 1a5b2ce114a0 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean has Deriv At poly R 1a5b2ce114a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanCalc.lean#L32-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanCalc
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0 (m : ℕ) (s : ℝ) : HasDerivAt (polyR m) (polyP m s) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«hasDerivAt_polyR» := P2M_GroundTheory_Heights__Heights_SphereMean_hasDerivAt_polyR_1a5b2ce114a0
