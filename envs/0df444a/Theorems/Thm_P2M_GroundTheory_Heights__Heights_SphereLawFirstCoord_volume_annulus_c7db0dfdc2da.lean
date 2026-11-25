-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:38:49.745089+00:00
-- url     : https://prove2.me/theorems/9170ed21-05be-41c6-b10e-3e2a2b46c1f0
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord volume annulus c7db0dfdc2da: P2 M Ground Theory Heights  Heights Sphere Law First Coord volume annulus c7db0dfdc2da
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord volume annulus c7db0dfdc2da construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord volume annulus c7db0dfdc2da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L17-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord
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
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    volume {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ENNReal.ofReal (s - a) * NNReal.pi := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«volume_annulus» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_annulus_c7db0dfdc2da
