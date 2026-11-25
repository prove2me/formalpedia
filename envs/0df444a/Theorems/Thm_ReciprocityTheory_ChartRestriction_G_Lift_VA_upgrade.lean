-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_upgrade
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.VA.upgrade
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:46.824521+00:00
-- url     : https://prove2.me/theorems/20894cee-d5e9-46e2-b3bc-c87001cef503
-- title:
--   VA: upgrade
-- statement:
--   The VA construction uses the upgrade property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L58-L66

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

theorem ReciprocityTheory.ChartRestriction.G.Lift.VA.upgrade (v w : Valuation Ω (WithZero (Multiplicative ℤ))) (π : Ω) (hπ : v π = exp (1 : ℤ))
    (u : Ω) (hu : 1 ≤ v u) (hu' : w u < 1) : ∃ x, 1 < v x ∧ w x < 1 := by sorry
