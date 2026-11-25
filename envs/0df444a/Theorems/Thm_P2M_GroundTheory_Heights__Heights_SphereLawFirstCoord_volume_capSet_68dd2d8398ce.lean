-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:39:04.995978+00:00
-- url     : https://prove2.me/theorems/d420f604-a397-5f8a-a80f-394e15f7ac79
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set 68dd2d8398ce: P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set 68dd2d8398ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set 68dd2d8398ce construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord volume cap Set 68dd2d8398ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L40-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L40-L73

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      (∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c))) * NNReal.pi := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«volume_capSet» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_volume_capSet_68dd2d8398ce
