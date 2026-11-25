-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_indicator_2f440d11df00
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_indicator_2f440d11df00
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:57:45.551091+00:00
-- url     : https://prove2.me/theorems/96f8efeb-2794-4a50-82c5-b0f522392534
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq smooth indicator 2f440d11df00: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq smooth indicator 2f440d11df00
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq smooth indicator 2f440d11df00 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq smooth indicator 2f440d11df00 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L57-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_indicator_2f440d11df00 (A : FinHolAtlas e X) {C : Set X} (hC : IsClopen C) {u : X → ℝ}
    (hu : A.Smooth u) : A.Smooth (C.indicator u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«smooth_indicator» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_smooth_indicator_2f440d11df00
