-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_comp_linearEquiv_50ba265b3ab6
-- name    : P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_comp_linearEquiv_50ba265b3ab6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:08.447179+00:00
-- url     : https://prove2.me/theorems/55858321-9b96-4026-9e44-9f37edfbf964
-- title:
--   P2 M Ground Theory Heights  Heights Sphere Mean set Average comp linear Equiv 50ba265b3ab6: P2 M Ground Theory Heights  Heights Sphere Mean set Average comp linear Equiv 50ba265b3ab6
-- statement:
--   The P2 M Ground Theory Heights  Heights Sphere Mean set Average comp linear Equiv 50ba265b3ab6 construction uses the P2 M Ground Theory Heights  Heights Sphere Mean set Average comp linear Equiv 50ba265b3ab6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/SphereMeanVol.lean#L30-L44

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_comp_linearEquiv_50ba265b3ab6 (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SphereMean».«setAverage_comp_linearEquiv» := P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_comp_linearEquiv_50ba265b3ab6
