-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_cardUX_lt
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hups_cardUX_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T06:07:01.753124+00:00
-- url     : https://prove2.me/theorems/152c54ec-328e-5e4b-b3e4-b3c2e030df16
-- title:
--   T0: hups card UX lt
-- statement:
--   The T0 construction uses the hups card UX lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/PolyL2EqSqrtCoeffSum.lean#L89-L101

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsTwCoeffCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_MinkSat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SatDegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PolyL2EqSqrtCoeffSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.hups_cardUX_lt (D N n n' deF u : ℕ) (h1 : 1 ≤ deF) (hn : deF ≤ n) :
    cardUX D N (n - deF) (n' - u) < cardUX D N n n' := by sorry
