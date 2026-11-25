-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:16.340555+00:00
-- url     : https://prove2.me/theorems/d4af4632-1a8f-46b7-8e7c-d05068056561
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord lintegral scale ed656ae4f52c: P2 M Ground Theory Heights  Heights Sphere Law First Coord lintegral scale ed656ae4f52c
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord lintegral scale ed656ae4f52c construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord lintegral scale ed656ae4f52c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L75-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L75-L98

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c {m : ℕ} {c : ℝ} (hc1 : c < 1) :
    ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c)) =
      ENNReal.ofReal ((1 - c) ^ m) * ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«lintegral_scale» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_lintegral_scale_ed656ae4f52c
