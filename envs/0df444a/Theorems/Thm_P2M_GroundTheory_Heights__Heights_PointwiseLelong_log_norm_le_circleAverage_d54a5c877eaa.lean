-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:50.295068+00:00
-- url     : https://prove2.me/theorems/18727a89-85e8-5686-b9d0-d01527cb41eb
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong log norm le circle Average d54a5c877eaa: P2 M Ground Theory Heights  Heights Pointwise Lelong log norm le circle Average d54a5c877eaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong log norm le circle Average d54a5c877eaa construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong log norm le circle Average d54a5c877eaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L40-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
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
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h0 : g 0 ≠ 0) :
    Real.log ‖g 0‖ ≤ circleAverage (fun z => Real.log ‖g z‖) 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«log_norm_le_circleAverage» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_log_norm_le_circleAverage_d54a5c877eaa
