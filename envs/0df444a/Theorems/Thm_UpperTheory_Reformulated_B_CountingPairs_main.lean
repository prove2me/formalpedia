-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_CountingPairs_main
-- name    : UpperTheory.Reformulated.B.CountingPairs.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:39:20.418199+00:00
-- url     : https://prove2.me/theorems/4c25a648-f1dd-462c-8705-995a3755102b
-- title:
--   Counting Pairs: main
-- statement:
--   The Counting Pairs construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CountingPairs.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CountingPairs.lean#L29-L43

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CountingPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open UpperTheory.Reformulated.B.CountingPairs.Priv

theorem UpperTheory.Reformulated.B.CountingPairs.main :
    ∀ {k : ℕ} (l : Fin k → ℤ),
      (∑ c : Fin k, ∑ i : Fin k, if i < c then l i - l c else (0 : ℤ)) = UpperTheory.Reformulated.B.CountingPairs.rhoPair l := by sorry
