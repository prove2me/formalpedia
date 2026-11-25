-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:40:06.890602+00:00
-- url     : https://prove2.me/theorems/149ee71d-b706-5fc3-9a3d-2784ccc3c241
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord law Ici f045ceeff4d1: P2 M Ground Theory Heights  Heights Sphere Law First Coord law Ici f045ceeff4d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord law Ici f045ceeff4d1 construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord law Ici f045ceeff4d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L144-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L144-L232

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1 (k : ℕ) (c : ℝ) :
    ((sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«law_Ici» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_law_Ici_f045ceeff4d1
