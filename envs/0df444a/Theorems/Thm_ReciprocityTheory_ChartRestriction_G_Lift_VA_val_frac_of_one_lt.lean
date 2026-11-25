-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_val_frac_of_one_lt
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_one_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:57.973264+00:00
-- url     : https://prove2.me/theorems/295a2c38-c02b-451a-8333-3fced3fa6a66
-- title:
--   VA: val frac of one lt
-- statement:
--   The VA construction uses the val frac of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L39-L47

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
variable {Ω : Type} [Field Ω]

theorem ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_one_lt (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : 1 < v y)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = 1 := by sorry
