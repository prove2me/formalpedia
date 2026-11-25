-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_twelve_dvd_five_pow_three_add_seven_pow_five
-- name    : ReciprocityTheory.ChartRestriction.L1.twelve_dvd_five_pow_three_add_seven_pow_five
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:47:31.196467+00:00
-- url     : https://prove2.me/theorems/32a1924f-d0b0-5b7f-b623-3e521d1ad8cc
-- title:
--   L1: twelve dvd five pow three add seven pow five
-- statement:
--   The L1 construction uses the twelve dvd five pow three add seven pow five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModDeltaInt.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModDeltaInt.lean#L11-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.twelve_dvd_five_pow_three_add_seven_pow_five (d : ℤ) : (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by sorry
