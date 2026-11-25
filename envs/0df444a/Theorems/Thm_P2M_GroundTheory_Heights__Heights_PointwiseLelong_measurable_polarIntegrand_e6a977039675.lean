-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:27.066327+00:00
-- url     : https://prove2.me/theorems/9cb1bae3-72d6-478f-9106-1a92ee87ba09
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Integrand e6a977039675: P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Integrand e6a977039675
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Integrand e6a977039675 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Integrand e6a977039675 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L187-L192

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675 (Q : MvPolynomial (Fin N) ℂ) (p : Fin N → ℂ) :
    Measurable (polarIntegrand Q p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«measurable_polarIntegrand» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675
