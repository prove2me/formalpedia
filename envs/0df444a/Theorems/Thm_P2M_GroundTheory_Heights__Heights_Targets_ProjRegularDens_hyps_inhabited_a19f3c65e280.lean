-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_hyps_inhabited_a19f3c65e280
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_hyps_inhabited_a19f3c65e280
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:35.010817+00:00
-- url     : https://prove2.me/theorems/ac994b74-b362-44f5-b7f3-40a912068af9
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Dens hyps inhabited a19f3c65e280: P2 M Ground Theory Heights  Heights Targets Proj Regular Dens hyps inhabited a19f3c65e280
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Dens hyps inhabited a19f3c65e280 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Dens hyps inhabited a19f3c65e280 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L131-L136

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_hyps_inhabited_a19f3c65e280 :
    (∀ j : Fin 0, IsSmoothHerm ((Fin.elim0 : Fin 0 → HermLine (PBlk 2)) j)) ∧
      HoloMap (ptAtlas ProjRegular.pointV) ProjectiveLineResolution.res.A Subtype.val ∧
      IsClosed ProjRegular.pointV ∧
      ∀ x ∈ ProjRegular.pointV, ProjRegular.projFirstCoordinate (segre (ProjectiveLineResolution.res.lift x x)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularDens».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_hyps_inhabited_a19f3c65e280
