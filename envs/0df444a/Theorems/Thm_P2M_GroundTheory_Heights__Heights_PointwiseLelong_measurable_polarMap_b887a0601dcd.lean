-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:20.701858+00:00
-- url     : https://prove2.me/theorems/2c5eca19-49f7-477b-91d4-a3c1f72e094b
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Map b887a0601dcd: P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Map b887a0601dcd
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Map b887a0601dcd construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong measurable polar Map b887a0601dcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L184-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L184-L185

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd (p : Fin N → ℂ) : Measurable (polarMap p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«measurable_polarMap» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd
