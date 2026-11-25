-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_prime_choice_class
-- name    : ReciprocityTheory.ChartRestriction.L1.prime_choice_class
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:57.772829+00:00
-- url     : https://prove2.me/theorems/4839d9ce-849f-43ae-966b-ad063bcb3d1f
-- title:
--   L1: prime choice class
-- statement:
--   The L1 construction uses the prime choice class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L7-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedPrime.lean#L7-L60

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

theorem ReciprocityTheory.ChartRestriction.L1.prime_choice_class (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ a : ℕ, a % 3 = 2 ∧ J((a : ℤ) | d) = 1 := by sorry
