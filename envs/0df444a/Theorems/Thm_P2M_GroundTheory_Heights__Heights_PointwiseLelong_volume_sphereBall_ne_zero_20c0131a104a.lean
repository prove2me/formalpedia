-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.105714+00:00
-- url     : https://prove2.me/theorems/f84270ba-47ce-4dc4-b42a-200bb9b997dc
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne zero 20c0131a104a: P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne zero 20c0131a104a
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne zero 20c0131a104a construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne zero 20c0131a104a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L109-L110

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a : volume (sphereBall (HermNorm.std N) 1) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«volume_sphereBall_ne_zero» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_zero_20c0131a104a
