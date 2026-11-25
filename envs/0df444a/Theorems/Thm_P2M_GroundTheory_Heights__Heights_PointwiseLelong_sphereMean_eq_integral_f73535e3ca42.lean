-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:54.580805+00:00
-- url     : https://prove2.me/theorems/165949c7-7e71-53e6-94f1-5b871bccb3d7
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Mean eq integral f73535e3ca42: P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Mean eq integral f73535e3ca42
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Mean eq integral f73535e3ca42 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong sphere Mean eq integral f73535e3ca42 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L123-L127

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42 {f : (Fin N → ℂ) → ℝ} (hf : Measurable f) :
    sphereMean (HermNorm.std N) 1 (fun u => f (fun j => u (0, j))) = ∫ z, f z ∂sphereLaw N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«sphereMean_eq_integral» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42
