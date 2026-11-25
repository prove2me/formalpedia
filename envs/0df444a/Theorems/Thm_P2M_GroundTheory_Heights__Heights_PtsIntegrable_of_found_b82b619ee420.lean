-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegrable_of_found_b82b619ee420
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegrable_of_found_b82b619ee420
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:15:47.930623+00:00
-- url     : https://prove2.me/theorems/7d184af4-2431-4551-a727-13e6374dd726
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integrable of found b82b619ee420: P2 M Ground Theory Heights  Heights Pts Integrable of found b82b619ee420
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integrable of found b82b619ee420 construction uses the P2 M Ground Theory Heights  Heights Pts Integrable of found b82b619ee420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsIntegrable.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsIntegrable.lean#L34-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StPtsAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_PtsIntegrable_of_found_b82b619ee420 (hAbs : Inter.PtsAbsIntegrable.Statement)
    (hMeas : PtsSumMeasurable.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegrable».«of_found» := P2M_GroundTheory_Heights__Heights_PtsIntegrable_of_found_b82b619ee420
