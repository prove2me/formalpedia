-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sum_mono_sq_div
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.sum_mono_sq_div
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:58.003007+00:00
-- url     : https://prove2.me/theorems/7f699d40-4825-4c2c-9151-07eed9c584d8
-- title:
--   Geometry Of Numbers Theory: sum mono sq div
-- statement:
--   The Geometry Of Numbers Theory construction uses the sum mono sq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L38-L42

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDefs
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_SupStMonoNormSqPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory

theorem ReciprocityTheory.GeometryOfNumbersTheory.sum_mono_sq_div (D n : ℕ) (z : Fin (D + 1) → ℂ) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * sqN z ^ n := by sorry
