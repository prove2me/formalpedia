-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:27.655784+00:00
-- url     : https://prove2.me/theorems/58b5690d-408f-487e-a07d-12fb438adef7
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean set Average smul measure fd7243322d3e: P2 M Ground Theory Heights  Heights Sphere Mean set Average smul measure fd7243322d3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean set Average smul measure fd7243322d3e construction uses the P2 M Ground Theory Heights  Heights Sphere Mean set Average smul measure fd7243322d3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L14-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
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
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean

theorem P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«setAverage_smul_measure» := P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e
