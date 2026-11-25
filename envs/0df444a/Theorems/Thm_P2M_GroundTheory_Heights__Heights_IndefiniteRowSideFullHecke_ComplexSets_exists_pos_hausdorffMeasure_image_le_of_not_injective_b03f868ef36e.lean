-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:43.201801+00:00
-- url     : https://prove2.me/theorems/73380680-9c20-4192-a9bd-49dea0f3a4f1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists pos hausdorff Measure image le of not injective b03f868ef36e: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists pos hausdorff Measure image le of not injective b03f868ef36e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists pos hausdorff Measure image le of not injective b03f868ef36e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L112-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L112-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e (f : (ι → ℝ) → F)
    (A : (ι → ℝ) →L[ℝ] F) (hA : ¬ Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
      μH[Fintype.card ι] (f '' t) ≤ ε * volume t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_pos_hausdorffMeasure_image_le_of_not_injective» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e
