-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_metric_0265930b243b
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_metric_0265930b243b
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:21.095867+00:00
-- url     : https://prove2.me/theorems/f0071633-90c6-5ae9-8542-4125ac774ee9
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line of Geo metric 0265930b243b: P2 M Ground Theory Heights  Heights Herm Line of Geo metric 0265930b243b
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line of Geo metric 0265930b243b construction uses the P2 M Ground Theory Heights  Heights Herm Line of Geo metric 0265930b243b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L191-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L191-L192

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
open GroundTheory.Heights₂.Heights.HermLine
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_metric_0265930b243b (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) (z : Cone n ℂ) :
    (ofGeo B hB).metric z = B.h (flatCone z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«ofGeo_metric» := P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_metric_0265930b243b
