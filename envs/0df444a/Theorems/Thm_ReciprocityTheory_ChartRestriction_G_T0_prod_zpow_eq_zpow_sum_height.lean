-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_prod_zpow_eq_zpow_sum_height
-- name    : ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq_zpow_sum_height
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:28:19.39723+00:00
-- url     : https://prove2.me/theorems/33b12c98-2455-4e68-a509-6178b80999b5
-- title:
--   T0: prod zpow eq zpow sum height
-- statement:
--   The T0 construction uses the prod zpow eq zpow sum height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ProdZpowEqZpowSum.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ProdZpowEqZpowSum.lean#L5-L10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockDegOfScale
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq_zpow_sum_height {M : Type*} [CommGroupWithZero M] {α : Type*}
    (s : Finset α) (f : α → ℤ) (a : M) (ha : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by sorry
