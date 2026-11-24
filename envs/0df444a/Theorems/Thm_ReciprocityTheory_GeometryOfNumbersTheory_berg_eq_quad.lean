-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_berg_eq_quad
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.berg_eq_quad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:01.556243+00:00
-- url     : https://prove2.me/theorems/df1d7c32-53ab-4d91-9c65-744a04a52679
-- title:
--   Geometry Of Numbers Theory: berg eq quad
-- statement:
--   The Geometry Of Numbers Theory construction uses the berg eq quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L143-L149

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.berg_eq_quad (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) :
    bergmanDensity μ s w x = w x * (star (star fun i => s i x) ⬝ᵥ (bGram μ s w)⁻¹ *ᵥ star fun i => s i x).re := by sorry
