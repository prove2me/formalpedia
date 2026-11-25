-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:20:53.740089+00:00
-- url     : https://prove2.me/theorems/205bc7ba-81b8-4321-bc00-3e12c3222908
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of approximates Linear On of mem ker aaa68814a6b5: P2 M Ground Theory Heights  Heights Indefi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of approximates Linear On of mem ker aaa68814a6b5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of approximates Linear On of mem ker aaa68814a6b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L40-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L40-L103

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5 {f : (ι → ℝ) → F}
    {A : (ι → ℝ) →L[ℝ] F} {k : ι → ℝ} {i0 : ι} (hk : A k = 0) (hki : k i0 = 1) {δ : ℝ≥0}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t : Set (ι → ℝ)} (ht : ApproximatesLinearOn f A t δ) :
    μH[Fintype.card ι] (f '' t) ≤
      ((Real.toNNReal (‖A‖ + 1 + ‖k‖) : ℝ≥0∞)) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ *
        volume t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5
