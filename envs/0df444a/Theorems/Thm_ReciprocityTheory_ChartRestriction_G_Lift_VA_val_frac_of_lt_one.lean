-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_val_frac_of_lt_one
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_lt_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:58.943965+00:00
-- url     : https://prove2.me/theorems/ca56f45c-d2ce-475f-97f6-59b701c4dad1
-- title:
--   VA: val frac of lt one
-- statement:
--   The VA construction uses the val frac of lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L49-L56

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

theorem ReciprocityTheory.ChartRestriction.G.Lift.VA.val_frac_of_lt_one (v : Valuation Ω (WithZero (Multiplicative ℤ))) (y : Ω) (hy : v y < 1)
    (m : ℕ) (hm : 1 ≤ m) : v (y ^ m / (1 + y ^ m)) = v y ^ m := by sorry
