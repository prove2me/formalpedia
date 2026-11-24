-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:33.25181+00:00
-- url     : https://prove2.me/theorems/3d2d1089-8a7e-40d6-aad0-57c59c74ef9d
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong measurable normalize 373300d892cc: P2 M Ground Theory Heights  Heights Pointwise Lelong measurable normalize 373300d892cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong measurable normalize 373300d892cc construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong measurable normalize 373300d892cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L103-L107

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc :
    Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) => sphereNormalize (HermNorm.std N) 1 u (0, j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«measurable_normalize» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_normalize_373300d892cc
