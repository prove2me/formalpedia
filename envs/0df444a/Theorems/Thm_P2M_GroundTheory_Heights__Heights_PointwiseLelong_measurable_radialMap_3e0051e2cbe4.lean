-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:39.359131+00:00
-- url     : https://prove2.me/theorems/2b4cfc49-4dc8-481e-ab29-2301b5a59380
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong measurable radial Map 3e0051e2cbe4: P2 M Ground Theory Heights  Heights Pointwise Lelong measurable radial Map 3e0051e2cbe4
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong measurable radial Map 3e0051e2cbe4 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong measurable radial Map 3e0051e2cbe4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L181-L182

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4 (p : Fin N → ℂ) : Measurable (radialMap p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«measurable_radialMap» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4
