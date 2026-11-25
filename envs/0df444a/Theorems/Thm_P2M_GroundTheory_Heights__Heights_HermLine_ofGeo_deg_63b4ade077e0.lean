-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_deg_63b4ade077e0
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_deg_63b4ade077e0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:13.339464+00:00
-- url     : https://prove2.me/theorems/a31bb985-8d5b-574b-b642-ac43927319d8
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line of Geo deg 63b4ade077e0: P2 M Ground Theory Heights  Heights Herm Line of Geo deg 63b4ade077e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line of Geo deg 63b4ade077e0 construction uses the P2 M Ground Theory Heights  Heights Herm Line of Geo deg 63b4ade077e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L187-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L187-L188

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

theorem P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_deg_63b4ade077e0 (B : Geo.HermLine (blockIdx n)) (hB : Geo.IsSmoothHerm B) :
    (ofGeo B hB).deg = B.a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«ofGeo_deg» := P2M_GroundTheory_Heights__Heights_HermLine_ofGeo_deg_63b4ade077e0
