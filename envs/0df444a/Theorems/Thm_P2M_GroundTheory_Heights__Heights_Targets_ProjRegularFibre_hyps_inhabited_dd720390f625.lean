-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_hyps_inhabited_dd720390f625
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_hyps_inhabited_dd720390f625
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:53:20.546746+00:00
-- url     : https://prove2.me/theorems/80d78ca7-38e9-50f6-a551-c5e5d9cf6d03
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre hyps inhabited dd720390f625: P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre hyps inhabited dd720390f625
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre hyps inhabited dd720390f625 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Fibre hyps inhabited dd720390f625 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L126-L129

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_hyps_inhabited_dd720390f625 :
    HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val ∧ IsClosed ProjRegular.pointV ∧
      ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularFibre».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularFibre_hyps_inhabited_dd720390f625
