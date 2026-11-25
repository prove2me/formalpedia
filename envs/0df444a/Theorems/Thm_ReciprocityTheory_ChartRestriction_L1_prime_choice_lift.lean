-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prime_choice_lift
-- name    : ReciprocityTheory.ChartRestriction.L1.prime_choice_lift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:33.834815+00:00
-- url     : https://prove2.me/theorems/4bc01d97-be52-57eb-a70b-c12d3fbbc15a
-- title:
--   L1: prime choice lift
-- statement:
--   The L1 construction uses the prime choice lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L71-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L71-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open scoped NumberTheorySymbols

theorem ReciprocityTheory.ChartRestriction.L1.prime_choice_lift (d p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hs : p ∣ s ^ 2 + d) : ∃ r : ℕ, Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by sorry
