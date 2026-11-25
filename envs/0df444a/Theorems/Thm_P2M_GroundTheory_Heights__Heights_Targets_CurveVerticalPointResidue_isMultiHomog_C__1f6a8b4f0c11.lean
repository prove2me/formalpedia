-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:50.824787+00:00
-- url     : https://prove2.me/theorems/9e1035a7-b64f-518f-b580-aab0536f526e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog C  1f6a8b4f0c11: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog C  1f6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog C  1f6a8b4f0c11 construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog C  1f6a8b4f0c11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointResidue
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Inter.AvoidRing
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11 (a : ℤ) : IsMultiHomog (C a : MRing ι) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«isMultiHomog_C'» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_C__1f6a8b4f0c11
