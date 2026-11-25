-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:14.547548+00:00
-- url     : https://prove2.me/theorems/b800100e-edd5-5d28-a2d9-313871ab4942
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst sub 5af0c3167cba: P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst sub 5af0c3167cba
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst sub 5af0c3167cba construction uses the P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst sub 5af0c3167cba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L14-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, (log ‖y 0‖ - log (sqNorm y) / 2) = -(harmonic m : ℝ) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«setAverage_log_fst_sub» := P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_sub_5af0c3167cba
