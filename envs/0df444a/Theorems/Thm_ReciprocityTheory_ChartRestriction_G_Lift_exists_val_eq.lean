-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Lift_exists_val_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:44:53.238456+00:00
-- url     : https://prove2.me/theorems/075492ec-0557-4be3-b20e-d8a68fabf82d
-- title:
--   Lift: exists val eq
-- statement:
--   The Lift construction uses the exists val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/RApprox.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ValuationLifting/RApprox.lean#L6-L10

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_ValApprox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ValuationLifting_RApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Lift

theorem ReciprocityTheory.ChartRestriction.G.Lift.exists_val_eq {Ω : Type} [Field Ω] {ι : Type} [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ)))
    (hgen : ∀ i, ∃ x, v i x = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hind : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) (n : ι → ℤ) :
    ∃ x : Ω, ∀ i, v i x = ((Multiplicative.ofAdd (n i) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by sorry
