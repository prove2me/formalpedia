-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:55:16.165488+00:00
-- url     : https://prove2.me/theorems/0c028a6f-a687-5203-9b51-66eb3e618e16
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential congr ae707927fd3e: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential congr ae707927fd3e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential congr ae707927fd3e construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Pos is Potential congr ae707927fd3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassPos.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassPos.lean#L18-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassPos
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassPos».«isPotential_congr» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassPos_isPotential_congr_ae707927fd3e
