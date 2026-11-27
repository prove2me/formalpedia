-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_card_support_le
-- name    : ReciprocityTheory.ChartRestriction.G.T0.card_support_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:03:00.9778+00:00
-- url     : https://prove2.me/theorems/c81fbefb-3ab5-5b5a-b679-f6c4da583bf2
-- title:
--   T0: card support le
-- statement:
--   The T0 construction uses the card support le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SumLeSqrtCardMul.lean#L8-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SumLeSqrtCardMul.lean#L8-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorHeightBound
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SumLeSqrtCardMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.card_support_le {R : Type*} [CommSemiring R] {D N n n' : ℕ}
    (Q : MvPolynomial (UXVar D N) R) (hx : XHom n Q) (hu : UDegLE n' Q) :
    Q.support.card ≤
      (n + D + 1).choose (D + 1) * (n' + (D + 2) * (N + 1)).choose ((D + 2) * (N + 1)) := by sorry
