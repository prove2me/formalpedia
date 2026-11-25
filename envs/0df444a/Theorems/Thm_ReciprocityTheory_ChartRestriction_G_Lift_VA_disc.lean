-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_disc
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.VA.disc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:58.479911+00:00
-- url     : https://prove2.me/theorems/3f628d43-8efc-4448-a1a5-f18246b5f18d
-- title:
--   VA: disc
-- statement:
--   The VA construction uses the disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L9-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_LiftSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_LargeSmall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValuationApproximation_RhoProjectionAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift ReciprocityTheory.ChartRestriction.G.Lift.VA
open WithZero

theorem ReciprocityTheory.ChartRestriction.G.Lift.VA.disc (M ε : WithZero (Multiplicative ℤ)) (hε : ε ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ m', m ≤ m' → ∀ g h : WithZero (Multiplicative ℤ),
      g < 1 → h ≤ M → g ^ m' * h < ε := by sorry
