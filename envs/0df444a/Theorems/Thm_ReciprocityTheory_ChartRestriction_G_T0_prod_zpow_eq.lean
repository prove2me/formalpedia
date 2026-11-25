-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_prod_zpow_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:20:12.421554+00:00
-- url     : https://prove2.me/theorems/36d4b8b5-4aad-4443-ad05-dd92988d229b
-- title:
--   T0: prod zpow eq
-- statement:
--   The T0 construction uses the prod zpow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAG.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAG.lean#L10-L15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain

theorem ReciprocityTheory.ChartRestriction.G.T0.prod_zpow_eq {ι G : Type*} [CommGroupWithZero G] {x : G} (hx : x ≠ 0) (s : Finset ι)
    (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by sorry
