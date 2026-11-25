-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_form_sq_le
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.form_sq_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:31.922251+00:00
-- url     : https://prove2.me/theorems/9eb04f55-b6b3-4875-8ad5-32c255bf0828
-- title:
--   Geometry Of Numbers Theory: form sq le
-- statement:
--   The Geometry Of Numbers Theory construction uses the form sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L116-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L116-L142

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.form_sq_le (D n : ℕ) (c : (Fin (D + 1) → ℕ) → ℂ) (z : Fin (D + 1) → ℂ) :
    ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a z‖ ^ 2 ≤
      ((n + D).choose D : ℝ) * sqN z ^ n *
        ∫ w, ‖∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, c a * monoC a w‖ ^ 2
          ∂(sphProb (D + 1)) := by sorry
