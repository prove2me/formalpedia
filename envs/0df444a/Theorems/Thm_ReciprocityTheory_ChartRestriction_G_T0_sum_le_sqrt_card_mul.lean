-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sum_le_sqrt_card_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.sum_le_sqrt_card_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:15:52.157896+00:00
-- url     : https://prove2.me/theorems/f6d42db8-bfc9-41da-b270-221137a0a5e4
-- title:
--   T0: sum le sqrt card mul
-- statement:
--   The T0 construction uses the sum le sqrt card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SumLeSqrtCardMul.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SumLeSqrtCardMul.lean#L52-L57

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

theorem ReciprocityTheory.ChartRestriction.G.T0.sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (a : α → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt s.card * Real.sqrt (∑ i ∈ s, a i ^ 2) := by sorry
