-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:39:28.548557+00:00
-- url     : https://prove2.me/theorems/c3d66c73-0ca5-591f-9b8b-681568f377a8
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential congr 7067f4d9748e: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential congr 7067f4d9748e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential congr 7067f4d9748e construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq is Potential congr 7067f4d9748e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L22-L31

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e (A : FinHolAtlas e X) {P Q : LocPot X} (hU : ∀ x, P.U x = Q.U x)
    (hφ : ∀ x, ∀ z ∈ P.U x, P.φ x z = Q.φ x z) (hP : IsPotential A P) : IsPotential A Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«isPotential_congr» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_isPotential_congr_7067f4d9748e
