-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_metricBound_iff_3bc934b867e5
-- name    : P2M_GroundTheory_Heights__Heights_metricBound_iff_3bc934b867e5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:53:09.797789+00:00
-- url     : https://prove2.me/theorems/1a8099ad-ff8b-539f-a5c7-366df1b115fa
-- title:
--   P2 M Ground Theory Heights  Heights metric Bound iff 3bc934b867e5: P2 M Ground Theory Heights  Heights metric Bound iff 3bc934b867e5
-- statement:
--   The P2 M Ground Theory Heights  Heights metric Bound iff 3bc934b867e5 construction uses the P2 M Ground Theory Heights  Heights metric Bound iff 3bc934b867e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L207-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L207-L218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_metricBound_iff_3bc934b867e5 (P : ArithVariety n) (A A' : HermLine n) (c : ℝ) :
    (∀ z ∈ Geo.mcPts (ι := blockIdx n) P.ideal,
        |Real.log (A.toGeo.h z / A'.toGeo.h z)| ≤ c) ↔
      ∀ z ∈ P.points ℂ, |Real.log (A.metric z) - Real.log (A'.metric z)| ≤ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«metricBound_iff» := P2M_GroundTheory_Heights__Heights_metricBound_iff_3bc934b867e5
