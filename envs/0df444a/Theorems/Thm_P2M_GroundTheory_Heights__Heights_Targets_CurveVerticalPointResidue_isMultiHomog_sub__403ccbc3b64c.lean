-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_sub__403ccbc3b64c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_sub__403ccbc3b64c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:51.921217+00:00
-- url     : https://prove2.me/theorems/225edcfa-befb-4697-aa14-b640bd61d1d6
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog sub  403ccbc3b64c: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog sub
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog sub  403ccbc3b64c construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Residue is Multi Homog sub  403ccbc3b64c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointResidue.lean#L22-L28

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_sub__403ccbc3b64c {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointResidue».«isMultiHomog_sub'» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointResidue_isMultiHomog_sub__403ccbc3b64c
