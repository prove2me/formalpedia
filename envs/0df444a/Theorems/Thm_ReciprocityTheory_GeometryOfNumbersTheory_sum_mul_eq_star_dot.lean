-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sum_mul_eq_star_dot
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sum_mul_eq_star_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:00.609003+00:00
-- url     : https://prove2.me/theorems/cf8ccf38-4215-4464-bd9a-2bdd552313fb
-- title:
--   Geometry Of Numbers Theory: sum mul eq star dot
-- statement:
--   The Geometry Of Numbers Theory construction uses the sum mul eq star dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanSt.lean#L151-L154

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.sum_mul_eq_star_dot {r : ℕ} (s : Fin r → X → ℂ) (c : Fin r → ℂ) (x : X) :
    ∑ i, c i * s i x = star (star fun i => s i x) ⬝ᵥ c := by sorry
