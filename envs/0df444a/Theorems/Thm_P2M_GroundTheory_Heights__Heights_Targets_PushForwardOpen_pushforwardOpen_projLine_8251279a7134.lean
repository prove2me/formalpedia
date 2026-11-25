-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_pushforwardOpen_projLine_8251279a7134
-- name    : P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_pushforwardOpen_projLine_8251279a7134
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:59.362213+00:00
-- url     : https://prove2.me/theorems/34c2d1a5-75bf-4069-9e01-b66626d18a74
-- title:
--   P2 M Ground Theory Heights  Heights Targets Push Forward Open pushforward Open proj Line 8251279a7134: P2 M Ground Theory Heights  Heights Targets Push Forward Open pushforward Open proj Line 8251279a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Push Forward Open pushforward Open proj Line 8251279a7134 construction uses the P2 M Ground Theory Heights  Heights Targets Push Forward Open pushforward Open proj Line 8251279a7134 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L84-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/DivPushResSideInhabitants.lean#L84-L90

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

theorem P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_pushforwardOpen_projLine_8251279a7134 (h : PushForwardOpen.Statement) :
    mInt p1 (fun _ : Fin 1 => fsPot) (fun _ => (1 : ℝ)) =
      ∫ y, ∑ᶠ x ∈ PushForwardOpen.projLineAffineCoordinate ⁻¹' {y} ∩ PushForwardOpen.finitePlane,
        (fun _ : OnePoint ℂ => (1 : ℝ)) x * pushDens p1 (fun _ : Fin 1 => fsPot)
          PushForwardOpen.projLineAffineCoordinate x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«PushForwardOpen».«pushforwardOpen_projLine» := P2M_GroundTheory_Heights__Heights_Targets_PushForwardOpen_pushforwardOpen_projLine_8251279a7134
