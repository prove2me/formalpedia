-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_applies_to_point_ddaee81f5d32
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_applies_to_point_ddaee81f5d32
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:00.124948+00:00
-- url     : https://prove2.me/theorems/75d53d30-7ddc-4287-8218-6047758074bf
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Regular Dens applies to point ddaee81f5d32: P2 M Ground Theory Heights  Heights Targets Proj Regular Dens applies to point ddaee81f5d32
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Regular Dens applies to point ddaee81f5d32 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Regular Dens applies to point ddaee81f5d32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L150-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L150-L159

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_applies_to_point_ddaee81f5d32 (h : ProjRegularDens.Statement) :
    ∀ j, ∀ᵐ u, u ∈ ((ptAtlas ProjRegular.pointV).chart j).target →
      ((ptAtlas ProjRegular.pointV).chart j).symm u ∉
        projRegular ProjectiveLineResolution.res ProjRegular.projFirstCoordinate (ptAtlas ProjRegular.pointV) →
      locDens (ptAtlas ProjRegular.pointV)
        (fun i => (potOf ProjectiveLineResolution.res ((Fin.elim0 : Fin 0 → HermLine (PBlk 2)) i)).pullback
          Subtype.val continuous_subtype_val) j u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjRegularDens».«applies_to_point» := P2M_GroundTheory_Heights__Heights_Targets_ProjRegularDens_applies_to_point_ddaee81f5d32
