-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_mInt_congr_6af1b6544da7
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_mInt_congr_6af1b6544da7
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:11.65575+00:00
-- url     : https://prove2.me/theorems/0fb91819-d42f-5ce4-81d2-8bb63a2a2755
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq m Int congr 6af1b6544da7: P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq m Int congr 6af1b6544da7
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq m Int congr 6af1b6544da7 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Pot Mass Eq m Int congr 6af1b6544da7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PProjPotMassEqGen.lean#L33-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotMassEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mInt_congr

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_mInt_congr_6af1b6544da7 (A : FinHolAtlas e X) (Φ Φ' : Fin e → LocPot X) (g : X → ℝ)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, g ((A.chart j).symm y) ≠ 0 →
      locDens A Φ j y = locDens A Φ' j y) : mInt A Φ g = mInt A Φ' g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjPotMassEq».«mInt_congr» := P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_mInt_congr_6af1b6544da7
