-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sq_le_berg_mul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sq_le_berg_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:25.610217+00:00
-- url     : https://prove2.me/theorems/062c6859-4bc2-463f-b8c1-2ed5ea2e5ee7
-- title:
--   Geometry Of Numbers Theory: sq le berg mul
-- statement:
--   The Geometry Of Numbers Theory construction uses the sq le berg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L156-L166

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sq_le_berg_mul (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (hpos : (bGram μ s w).PosDef) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x ≤ bergmanDensity μ s w x * bNormSq μ s w c := by sorry
