-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_VA_large_small_separation
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:31:29.272824+00:00
-- url     : https://prove2.me/theorems/37cf9c1d-80ce-4c51-a87d-ec2176d1022f
-- title:
--   VA: large small separation
-- statement:
--   The VA construction uses the large small separation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L109-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/ValuationApproximation/RhoProjectionAssembly.lean#L109-L149

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

theorem ReciprocityTheory.ChartRestriction.G.Lift.VA.large_small_separation : LargeSmall := by sorry
