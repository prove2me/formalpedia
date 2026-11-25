-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prime_choice
-- name    : ReciprocityTheory.ChartRestriction.L1.prime_choice
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:51.285871+00:00
-- url     : https://prove2.me/theorems/539548c3-a8cc-4bba-8e1f-bb4c07c72845
-- title:
--   L1: prime choice
-- statement:
--   The L1 construction uses the prime choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L105-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L105-L140

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

theorem ReciprocityTheory.ChartRestriction.L1.prime_choice (d b : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ p r : ℕ, p.Prime ∧ b < p ∧ d < p ∧ p % 3 = 2 ∧ Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by sorry
