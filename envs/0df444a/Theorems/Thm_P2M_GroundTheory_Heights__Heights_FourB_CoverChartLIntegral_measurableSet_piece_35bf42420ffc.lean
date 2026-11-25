-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:48.186229+00:00
-- url     : https://prove2.me/theorems/bc1ed7f6-92b3-49de-8d46-6b594cda0bfe
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral measurable Set piece 35bf42420ffc: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral measurable Set piece 35bf42420ffc
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral measurable Set piece 35bf42420ffc construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral measurable Set piece 35bf42420ffc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L148-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L148-L160

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W) (hWM : W ⊆ M₀)
    {B : Set (Fin e → ℂ)} (hB : MeasurableSet B) :
    MeasurableSet (((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩
      (q ∘ (A.chart j).symm) ⁻¹' B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«measurableSet_piece» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc
