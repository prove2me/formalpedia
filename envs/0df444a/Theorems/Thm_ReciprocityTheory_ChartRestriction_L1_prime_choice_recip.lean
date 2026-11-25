-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prime_choice_recip
-- name    : ReciprocityTheory.ChartRestriction.L1.prime_choice_recip
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:39.58989+00:00
-- url     : https://prove2.me/theorems/1ccd8b60-2117-5649-b00d-abb170fa333c
-- title:
--   L1: prime choice recip
-- statement:
--   The L1 construction uses the prime choice recip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L62-L69

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

theorem ReciprocityTheory.ChartRestriction.L1.prime_choice_recip (d p : ℕ) (hd4 : d % 4 = 3) (hp : Odd p) :
    J(-(d : ℤ) | p) = J((p : ℤ) | d) := by sorry
