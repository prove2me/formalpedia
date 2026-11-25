-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_massIndep_clopen_929448047c99
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_massIndep_clopen_929448047c99
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:45:51.81394+00:00
-- url     : https://prove2.me/theorems/af82023f-f77a-5c65-abf3-dd98c397f60c
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq mass Indep clopen 929448047c99: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq mass Indep clopen 929448047c99
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq mass Indep clopen 929448047c99 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq mass Indep clopen 929448047c99 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L70-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L70-L116

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_massIndep_clopen_929448047c99 [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) {Φ : LocPot X}
    (hΦ : IsPotential A Φ) (Θ : LocPot X) (u : X → ℝ) (hu : A.Smooth u) {C : Set X}
    (hC : IsClopen C)
    (hΘ : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ C →
      locDens A (fun _ => Θ) j y = locDens A (fun _ => Φ + LocPot.ofFun u) j y) :
    mInt A (fun _ => Φ) (C.indicator fun _ => (1 : ℝ)) =
      mInt A (fun _ => Θ) (C.indicator fun _ => (1 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«massIndep_clopen» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_massIndep_clopen_929448047c99
