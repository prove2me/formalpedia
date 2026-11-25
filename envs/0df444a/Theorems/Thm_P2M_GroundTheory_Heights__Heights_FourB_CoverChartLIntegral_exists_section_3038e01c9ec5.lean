-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_section_3038e01c9ec5
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_section_3038e01c9ec5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:21.130876+00:00
-- url     : https://prove2.me/theorems/aa20bbc6-2fb7-51fc-a903-66f200f8b884
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists section 3038e01c9ec5: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists section 3038e01c9ec5
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists section 3038e01c9ec5 construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists section 3038e01c9ec5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L102-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L102-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
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
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_section_3038e01c9ec5 [Nonempty X] {q : X → Fin e → ℂ} {W : Set X} {U : Set (Fin e → ℂ)}
    (hopen : ∀ O : Set X, IsOpen O → O ⊆ W → IsOpen (q '' O)) (hW : IsOpen W)
    (hbij : Set.BijOn q W U) :
    ∃ s : (Fin e → ℂ) → X, ContinuousOn s U ∧ (∀ u ∈ U, s u ∈ W ∧ q (s u) = u) ∧
      ∀ x ∈ W, s (q x) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«exists_section» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_section_3038e01c9ec5
