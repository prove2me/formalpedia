-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bNormSq_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.bNormSq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:56.151002+00:00
-- url     : https://prove2.me/theorems/6965a46d-46d5-436b-920e-73cb9ed49dff
-- title:
--   Geometry Of Numbers Theory: b Norm Sq eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the b Norm Sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L99-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L99-L129

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.bNormSq_eq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ)
    (c : Fin r → ℂ) :
    (bNormSq μ s w c : ℂ) = ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * bGram μ s w i j := by sorry
