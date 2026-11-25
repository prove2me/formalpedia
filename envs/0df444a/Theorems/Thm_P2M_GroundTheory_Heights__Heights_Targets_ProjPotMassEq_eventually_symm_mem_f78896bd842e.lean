-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:54:34.579812+00:00
-- url     : https://prove2.me/theorems/0719dedb-99e3-583d-bc21-f1beb5502b9a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq eventually symm mem f78896bd842e: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq eventually symm mem f78896bd842e
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq eventually symm mem f78896bd842e construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq eventually symm mem f78896bd842e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L52-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L52-L55

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e (A : FinHolAtlas e X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) {S : Set X} (hS : IsOpen S) (hyS : (A.chart j).symm y ∈ S) :
    ∀ᶠ y' in 𝓝 y, (A.chart j).symm y' ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«eventually_symm_mem» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_eventually_symm_mem_f78896bd842e
