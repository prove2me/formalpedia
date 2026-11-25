-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:19.784887+00:00
-- url     : https://prove2.me/theorems/dc395635-7e31-4f31-834d-e4155ae90e91
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne top d0ba649bf8e6: P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne top d0ba649bf8e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne top d0ba649bf8e6 construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong volume sphere Ball ne top d0ba649bf8e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L112-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L112-L113

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

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6 : volume (sphereBall (HermNorm.std N) 1) ≠ ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«volume_sphereBall_ne_top» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_volume_sphereBall_ne_top_d0ba649bf8e6
