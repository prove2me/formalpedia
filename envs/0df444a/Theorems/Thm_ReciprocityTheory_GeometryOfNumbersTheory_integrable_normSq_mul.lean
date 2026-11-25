-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integrable_normSq_mul
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integrable_normSq_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:08.179861+00:00
-- url     : https://prove2.me/theorems/cb269ad3-43fe-432f-a33d-46f43c42f096
-- title:
--   Geometry Of Numbers Theory: integrable norm Sq mul
-- statement:
--   The Geometry Of Numbers Theory construction uses the integrable norm Sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L44-L50

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
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

theorem ReciprocityTheory.GeometryOfNumbersTheory.integrable_normSq_mul (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) : Integrable (fun x => ‖∑ i, c i * s i x‖ ^ 2 * w x) μ := by sorry
