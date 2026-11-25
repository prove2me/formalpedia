-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_supSt_term
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.supSt_term
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:52.448125+00:00
-- url     : https://prove2.me/theorems/2e2fa5dc-c0b8-418f-9229-ba8d25918f77
-- title:
--   Geometry Of Numbers Theory: sup St term
-- statement:
--   The Geometry Of Numbers Theory construction uses the sup St term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/SupStMonoNormSqPos.lean#L13-L36

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.supSt_term {D n : ℕ} (a : Fin (D + 1) → ℕ) (ha : ∑ i, a i = n) (z : Fin (D + 1) → ℂ) :
    ‖monoC a z‖ ^ 2 / monoNormSq a =
      ((n + D).choose D : ℝ) * ((Nat.multinomial Finset.univ a : ℕ) *
        ∏ i, (‖z i‖ ^ 2) ^ a i) := by sorry
