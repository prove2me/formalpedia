-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:33.0858+00:00
-- url     : https://prove2.me/theorems/e8376c00-a52f-44c5-aaf9-8b8fad7cb4dc
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong measurable ortho Dir 50f4f53cb25a: P2 M Ground Theory Heights  Heights Pointwise Lelong measurable ortho Dir 50f4f53cb25a
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong measurable ortho Dir 50f4f53cb25a construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong measurable ortho Dir 50f4f53cb25a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L166-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L166-L170

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a (p : Fin N → ℂ) : Measurable (orthoDir p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«measurable_orthoDir» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_orthoDir_50f4f53cb25a
