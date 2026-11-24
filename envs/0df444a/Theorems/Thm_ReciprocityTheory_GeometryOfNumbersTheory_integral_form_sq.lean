-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_form_sq
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_form_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:59.736801+00:00
-- url     : https://prove2.me/theorems/abee2858-7390-4adb-89ef-1cb01e145d0b
-- title:
--   Geometry Of Numbers Theory: integral form sq
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral form sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L80-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L80-L108

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_form_sq (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) :
    ∫ z, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ∂(sphProb (D + 1)) =
      ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, ‖c a‖ ^ 2 * monoNormSq a := by sorry
