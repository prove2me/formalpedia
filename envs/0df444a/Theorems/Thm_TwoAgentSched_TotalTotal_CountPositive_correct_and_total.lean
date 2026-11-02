-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_CountPositive_correct_and_total
-- name    : TwoAgentSched.TotalTotal.CountPositive.correct_and_total
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:40:50.689625+00:00
-- url     : https://prove2.me/theorems/c2036d88-41e1-46f3-a37d-c804c9e8e685
-- title:
--   Counting nonzero binary blocks: correctness and total time bound
-- statement:
--   The positive-block counter has two properties.
--
--   1. On the canonical encoding of a finite list of natural weights, with an initial success marker, it consumes all blocks and adds one unary count marker for each nonzero weight. It records two success markers per parsed block and halts in at most $14|w|+1$ source steps, where $w$ is the encoded input.
--   2. For every symbol input and every initial status and count stack, including malformed or truncated input, it terminates within $10(|w|+1)^2$ source steps.
--
--   The counter supplies the number of positive weights used by the no-sort ordered PARTITION gadget. The second clause establishes termination only; the complete reduction still must reject malformed words and actually remove zero weights.
-- source:
--   Supporting implementation for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This counter and its bounds are additional formalization results, not claims of the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_CountPositive

namespace TwoAgentSched.TotalTotal.CountPositive

open CookPvsNP ProjSchedTW.Complexity

theorem correct_and_total :
    (∀ (xs : List ℕ) (status count : List BSym), status.head? = some .one →
      ∃ steps : ℕ,
        countPositive.Exec (store4 (encNats xs) [] status count)
          (store4 [] [] (List.replicate (2 * xs.length) .one ++ status)
            (List.replicate (xs.filter (fun m => m ≠ 0)).length .one ++ count)) steps ∧
        steps ≤ 14 * (encNats xs).length + 1) ∧
    (∀ input status count : List BSym, ∃ (out : Fin 4 → List BSym) (steps : ℕ),
      countPositive.Exec (store4 input [] status count) out steps ∧
        steps ≤ 10 * (input.length + 1) ^ 2) := by sorry

end TwoAgentSched.TotalTotal.CountPositive
