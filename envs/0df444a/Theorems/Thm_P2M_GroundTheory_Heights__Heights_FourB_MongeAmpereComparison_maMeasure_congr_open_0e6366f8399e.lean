-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e
-- name    : P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:36:22.649685+00:00
-- url     : https://prove2.me/theorems/3c496738-a309-49f0-b079-56da8f6c5675
-- title:
--   P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure congr open 0e6366f8399e: P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure congr open 0e6366f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure congr open 0e6366f8399e construction uses the P2 M Ground Theory Heights  Heights Four B Monge Ampere Comparison ma Measure congr open 0e6366f8399e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L143-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PMongeAmpereComparison.lean#L143-L166

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison

theorem P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) {S : Set X} (hS : IsOpen S)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ S →
      locDens A Φ j y = locDens A Ψ j y) :
    maMeasure A Φ S = maMeasure A Ψ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«MongeAmpereComparison».«maMeasure_congr_open» := P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e
