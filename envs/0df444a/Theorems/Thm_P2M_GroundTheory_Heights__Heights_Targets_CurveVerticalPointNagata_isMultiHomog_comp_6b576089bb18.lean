-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_isMultiHomog_comp_6b576089bb18
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_isMultiHomog_comp_6b576089bb18
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:06.213794+00:00
-- url     : https://prove2.me/theorems/347816be-36bc-5228-acd0-a82020d2a985
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata is Multi Homog comp 6b576089bb18: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata is Multi Homog comp 6b
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata is Multi Homog comp 6b576089bb18 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Nagata is Multi Homog comp 6b576089bb18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointNagata.lean#L28-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointNagata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_isMultiHomog_comp_6b576089bb18 (e : K → ℕ) (f : MRing ι) : IsMultiHomog (comp e f) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointNagata».«isMultiHomog_comp» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_isMultiHomog_comp_6b576089bb18
