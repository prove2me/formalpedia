-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654
-- name    : P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:59.462418+00:00
-- url     : https://prove2.me/theorems/1c1b6482-49bc-4879-b31e-79eb85fd6605
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Law First Coord density Ici 1e097aef9654: P2 M Ground Theory Heights  Heights Sphere Law First Coord density Ici 1e097aef9654
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Law First Coord density Ici 1e097aef9654 construction uses the P2 M Ground Theory Heights  Heights Sphere Law First Coord density Ici 1e097aef9654 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawFirstCoord.lean#L112-L142

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

theorem P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654 (k : ℕ) (c : ℝ) :
    (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal
        (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereLawFirstCoord».«density_Ici» := P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654
