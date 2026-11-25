-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:04.074651+00:00
-- url     : https://prove2.me/theorems/38a4f16f-fce0-4716-9275-f7e6fe110909
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of not injective ball 56dba06368fb: P2 M Ground Theory Heights  Heights Indefinite Row Side F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of not injective ball 56dba06368fb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hausdorff Measure image le of not injective ball 56dba06368fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L149-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCriticalImageNull.lean#L149-L186

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
variable [SecondCountableTopology F]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) (R : ℝ) (hs : s ⊆ closedBall 0 R)
    (ε : ℝ≥0) (εpos : 0 < ε) :
    μH[Fintype.card ι] (f '' s) ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«hausdorffMeasure_image_le_of_not_injective_ball» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb
