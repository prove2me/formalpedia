-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:57.066963+00:00
-- url     : https://prove2.me/theorems/2743d697-fa69-4f5f-a594-4591b0a91e9b
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong main bound fdf9c91e7ac8: P2 M Ground Theory Heights  Heights Pointwise Lelong main bound fdf9c91e7ac8
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong main bound fdf9c91e7ac8 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong main bound fdf9c91e7ac8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L194-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L194-L291

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8 (h1 : SphereProjectionLaw.Statement) {d : ℕ} {Q : MvPolynomial (Fin N) ℂ}
    (hQ0 : Q ≠ 0) (hQ : Q.IsHomogeneous d) (p : Fin N → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hQp : eval p Q ≠ 0) :
    Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2 ≤
      sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«main_bound» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8
