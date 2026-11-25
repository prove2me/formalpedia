-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HNm_nonneg_of_isIntegral
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HNm.nonneg_of_isIntegral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:18.541624+00:00
-- url     : https://prove2.me/theorems/b9d8adb2-a19f-583b-9b7e-070259f8c763
-- title:
--   HNm: nonneg of is Integral
-- statement:
--   The HNm construction uses the nonneg of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormA.lean#L19-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HNormA.lean#L19-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HNm

theorem ReciprocityTheory.ChartRestriction.G.T0.HNm.nonneg_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : AddValuation L (WithTop ℤ)) (h0 : ∀ r : R, 0 ≤ w (algebraMap R L r)) {x : L}
    (hx : IsIntegral R x) : 0 ≤ w x := by sorry
