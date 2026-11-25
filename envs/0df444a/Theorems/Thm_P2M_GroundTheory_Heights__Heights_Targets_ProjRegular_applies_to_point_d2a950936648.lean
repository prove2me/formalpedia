-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_applies_to_point_d2a950936648
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_applies_to_point_d2a950936648
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:46:59.3923+00:00
-- url     : https://prove2.me/theorems/d8e2110a-5d94-46c2-942b-c7531d2473ee
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular applies to point d2a950936648: P2 M Ground Theory Heights  Heights Targets Proj Regular applies to point d2a950936648
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular applies to point d2a950936648 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular applies to point d2a950936648 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L138-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_KerEqBotOfCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegularDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_DivPushResSideInhabitants
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_applies_to_point_d2a950936648 (h : ProjRegular.Statement) :
    IsOpen (projRegular ProjectiveLineResolution.res ProjRegular.projFirstCoordinate (ptAtlas ProjRegular.pointV)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegular».«applies_to_point» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_applies_to_point_d2a950936648
