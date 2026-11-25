-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea
-- name    : P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:28:11.749376+00:00
-- url     : https://prove2.me/theorems/4c7e9449-bdce-4733-8ee8-898776e819fb
-- title:
--   P2 M Ground Theory Heights  Heights Log Int scale in Group apply same c953392429ea: P2 M Ground Theory Heights  Heights Log Int scale in Group apply same c953392429ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Log Int scale in Group apply same c953392429ea construction uses the P2 M Ground Theory Heights  Heights Log Int scale in Group apply same c953392429ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogIntSphere.lean#L98-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea (i : Fin k) (c : ℂ) (u : Fin k × Fin n → ℂ) (j : Fin n) :
    scaleP (inGroup i) c u (i, j) = c * u (i, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LogInt».«scale_inGroup_apply_same» := P2M_GroundTheory_Heights__Heights_LogInt_scale_inGroup_apply_same_c953392429ea
