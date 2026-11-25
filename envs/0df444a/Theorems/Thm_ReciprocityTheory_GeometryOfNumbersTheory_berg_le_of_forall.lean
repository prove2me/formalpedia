-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_berg_le_of_forall
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.berg_le_of_forall
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:42.017524+00:00
-- url     : https://prove2.me/theorems/35e7a242-c27a-4798-8845-a70f0e2f32df
-- title:
--   Geometry Of Numbers Theory: berg le of forall
-- statement:
--   The Geometry Of Numbers Theory construction uses the berg le of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L168-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L168-L188

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]

theorem ReciprocityTheory.GeometryOfNumbersTheory.berg_le_of_forall (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (x : X) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ c : Fin r → ℂ, ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ M * bNormSq μ s w c) :
    bergmanDensity μ s w x ≤ M := by sorry
