-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_congr_metric_78f42bd42780
-- name    : P2M_GroundTheory_Heights__Heights_height_congr_metric_78f42bd42780
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:47:43.799394+00:00
-- url     : https://prove2.me/theorems/d08d87a2-03ae-4178-9641-f43a3313c54d
-- title:
--   P2 M Ground Theory Heights  Heights height congr metric 78f42bd42780: P2 M Ground Theory Heights  Heights height congr metric 78f42bd42780
-- statement:
--   The P2 M Ground Theory Heights  Heights height congr metric 78f42bd42780 construction uses the P2 M Ground Theory Heights  Heights height congr metric 78f42bd42780 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L222-L229

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_height_congr_metric_78f42bd42780 {A A' : HermLine n} (hdeg : A.deg = A'.deg)
    (hm : ∀ z : Cone n ℂ, BlockNonzero z → A.metric z = A'.metric z)
    {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) : height A x = height A' x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_congr_metric» := P2M_GroundTheory_Heights__Heights_height_congr_metric_78f42bd42780
