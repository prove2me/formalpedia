-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_normalized_c0546c37a0db
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_normalized_c0546c37a0db
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:12.303782+00:00
-- url     : https://prove2.me/theorems/244d13f3-2201-4bdd-b85c-d2e28f8c154e
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst normalized c0546c37a0db: P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst normalized c0546c37a0db
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst normalized c0546c37a0db construction uses the P2 M Ground Theory Heights  Heights Sphere Mean set Average log fst normalized c0546c37a0db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMean.lean#L45-L57

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

theorem P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_normalized_c0546c37a0db (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, log ‖((√(sqNorm y) : ℝ) : ℂ)⁻¹ * y 0‖ = -(harmonic m : ℝ) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«setAverage_log_fst_normalized» := P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_log_fst_normalized_c0546c37a0db
