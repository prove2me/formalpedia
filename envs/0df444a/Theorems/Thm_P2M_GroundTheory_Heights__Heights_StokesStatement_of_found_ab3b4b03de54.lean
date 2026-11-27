-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StokesStatement_of_found_ab3b4b03de54
-- name    : P2M_GroundTheory_Heights__Heights_StokesStatement_of_found_ab3b4b03de54
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:35.07446+00:00
-- url     : https://prove2.me/theorems/70dab5c2-bd94-5baa-bfbe-b5fcaf4d32c4
-- title:
--   P2 M Ground Theory Heights  Heights Stokes Statement of found ab3b4b03de54: P2 M Ground Theory Heights  Heights Stokes Statement of found ab3b4b03de54
-- statement:
--   The P2 M Ground Theory Heights  Heights Stokes Statement of found ab3b4b03de54 construction uses the P2 M Ground Theory Heights  Heights Stokes Statement of found ab3b4b03de54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/Stokes.lean#L13-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/Stokes.lean#L13-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_Stokes
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

theorem P2M_GroundTheory_Heights__Heights_StokesStatement_of_found_ab3b4b03de54 (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StokesStatement».«of_found» := P2M_GroundTheory_Heights__Heights_StokesStatement_of_found_ab3b4b03de54
