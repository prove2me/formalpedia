-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:14.46101+00:00
-- url     : https://prove2.me/theorems/ec174421-63d9-50ee-8627-bdb7936c38b2
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit C loc B c0010f784358: P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit C loc B c0010f784358
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit C loc B c0010f784358 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Mult is Unit C loc B c0010f784358 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMult.lean#L71-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
omit [Fintype ι] [DecidableEq ι] [IsDomain O]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358 (m : Ideal O) [m.IsPrime] (u : m.primeCompl) :
    IsUnit (((algebraMap (MvPolynomial ι O) (locB ι m)).comp C) (u : O)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMult».«isUnit_C_locB» := P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358
