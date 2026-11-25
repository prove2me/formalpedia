-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5
-- name    : P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:24.213843+00:00
-- url     : https://prove2.me/theorems/71db230b-8ce2-4478-aa01-a3bfcd9ed482
-- title:
--   P2 M Ground Theory Heights  Heights Herm Line to Geo of Geo h 01fd03adcfe5: P2 M Ground Theory Heights  Heights Herm Line to Geo of Geo h 01fd03adcfe5
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Line to Geo of Geo h 01fd03adcfe5 construction uses the P2 M Ground Theory Heights  Heights Herm Line to Geo of Geo h 01fd03adcfe5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Reading.lean#L49-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5 (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N)
    {w : Coord n → ℂ} (hw : BlockNonzero (unflatCone w)) : (HermLine.ofGeo N hN).toGeo.h w = N.h w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermLine».«toGeo_ofGeo_h» := P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5
