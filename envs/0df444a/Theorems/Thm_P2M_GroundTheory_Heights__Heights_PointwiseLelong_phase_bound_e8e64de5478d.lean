-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:51.780348+00:00
-- url     : https://prove2.me/theorems/500e52e6-16f7-4615-a7f3-0d9e817efbef
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong phase bound e8e64de5478d: P2 M Ground Theory Heights  Heights Pointwise Lelong phase bound e8e64de5478d
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong phase bound e8e64de5478d construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong phase bound e8e64de5478d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L61-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L61-L101

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d {Q : MvPolynomial (Fin N) ℂ} {d : ℕ} (hQ : Q.IsHomogeneous d)
    (p t : Fin N → ℂ) (hp : eval p Q ≠ 0) {r : ℝ} (hr : 0 < r) (b : ℝ) :
    Real.log ‖eval p Q‖ + d * Real.log r ≤
      ∫ θ, Real.log ‖eval (((r : ℂ) * Complex.exp (θ * Complex.I)) • p + (b : ℂ) • t) Q‖ ∂phaseLaw := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«phase_bound» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d
