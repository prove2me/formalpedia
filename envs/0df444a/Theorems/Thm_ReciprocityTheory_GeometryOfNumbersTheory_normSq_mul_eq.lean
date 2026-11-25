-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_normSq_mul_eq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.normSq_mul_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:53:41.304885+00:00
-- url     : https://prove2.me/theorems/7818a22b-30b9-43e2-b611-e5a17ca01ab1
-- title:
--   Geometry Of Numbers Theory: norm Sq mul eq
-- statement:
--   The Geometry Of Numbers Theory construction uses the norm Sq mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean#L31-L42

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.normSq_mul_eq {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) (x : X) :
    ‖∑ i, c i * s i x‖ ^ 2 * w x =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (starRingEnd ℂ (s i x) * s j x * (w x : ℂ))).re := by sorry
