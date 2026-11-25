-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:36.27628+00:00
-- url     : https://prove2.me/theorems/c6308c13-5d50-41e9-88af-974c4e6346ac
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong eval ne zero of max d14cb858f69d: P2 M Ground Theory Heights  Heights Pointwise Lelong eval ne zero of max d14cb858f69d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong eval ne zero of max d14cb858f69d construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong eval ne zero of max d14cb858f69d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L318-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L318-L346

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d {d : ℕ} {Q : MvPolynomial (Fin N) ℂ} (hQ0 : Q ≠ 0)
    (hQ : Q.IsHomogeneous d) {p : Fin N → ℂ} (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hmax : ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖) : eval p Q ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«eval_ne_zero_of_max» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_ne_zero_of_max_d14cb858f69d
