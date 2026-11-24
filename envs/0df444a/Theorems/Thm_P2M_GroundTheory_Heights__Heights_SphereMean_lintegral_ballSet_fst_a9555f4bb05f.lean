-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:34.468708+00:00
-- url     : https://prove2.me/theorems/f9f11b68-1943-4176-8e6d-6c6e70a6d227
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set fst a9555f4bb05f: P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set fst a9555f4bb05f
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set fst a9555f4bb05f construction uses the P2 M Ground Theory Heights  Heights Sphere Mean lintegral ball Set fst a9555f4bb05f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L23-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanSlice.lean#L23-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
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
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f (m : ℕ) (φ : ℂ → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x in ballSet (m + 1) 1, φ (x 0) =
      (∫⁻ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal ((1 - r ^ 2) ^ m)) ‖z‖ * φ z) *
        volume (ballSet m 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«lintegral_ballSet_fst» := P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_fst_a9555f4bb05f
