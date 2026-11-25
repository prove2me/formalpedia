-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:30.022201+00:00
-- url     : https://prove2.me/theorems/d1155964-6481-4743-939a-4f521ac51b2f
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line log div to Geo h fb686777305f: P2 M Ground Theory Heights  Heights Herm Line log div to Geo h fb686777305f
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line log div to Geo h fb686777305f construction uses the P2 M Ground Theory Heights  Heights Herm Line log div to Geo h fb686777305f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L198-L203

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

theorem P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f (A A' : HermLine n) {z : Cone n ℂ} (hz : BlockNonzero z) :
    Real.log (A.toGeo.h (flatCone z) / A'.toGeo.h (flatCone z)) =
      Real.log (A.metric z) - Real.log (A'.metric z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«log_div_toGeo_h» := P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f
