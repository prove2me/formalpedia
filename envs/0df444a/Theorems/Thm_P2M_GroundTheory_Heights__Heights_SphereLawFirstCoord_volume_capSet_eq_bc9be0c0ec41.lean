-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:08.375191+00:00
-- url     : https://prove2.me/theorems/cabf1b72-23a7-5052-b13f-873de1a46d8c
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set eq bc9be0c0ec41: P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set eq bc9be0c0ec41
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set eq bc9be0c0ec41 construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set eq bc9be0c0ec41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L100-L110

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41 {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ENNReal.ofReal ((1 - c) ^ m) * volume (ballSet (m + 1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«volume_capSet_eq» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_eq_bc9be0c0ec41
