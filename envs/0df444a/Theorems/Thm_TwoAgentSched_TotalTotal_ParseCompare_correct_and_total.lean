-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_ParseCompare_correct_and_total
-- name    : TwoAgentSched.TotalTotal.ParseCompare.correct_and_total
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T20:42:51.655047+00:00
-- url     : https://prove2.me/theorems/9b72cb1b-3f5b-4974-ba24-bda4c56adfc3
-- title:
--   Parsing and comparing two canonical binary naturals takes linear stack time
-- statement:
--   The five-stack parser/comparator has two properties.
--
--   1. Given canonical natural-number codes $\operatorname{enc}(m)\operatorname{enc}(n)$ followed by any suffix $u$, it consumes the two blocks, leaves $u$ unread, and puts a less marker at the top of its result stack exactly when $m<n$. It takes at most
--
--   $$
--   3|\operatorname{bits}(m)|+3|\operatorname{bits}(n)|
--    +3\min(|\operatorname{bits}(m)|,|\operatorname{bits}(n)|)+21
--   $$
--
--   source steps.
--   2. On every input word $w$, including malformed or truncated codes, it terminates within $9|w|+21$ source steps.
--
--   This is a reusable comparison component for a binary scheduling reduction. The second statement establishes termination only; it does not assert that the component rejects malformed input or that a complete sorting transducer has been built.
-- source:
--   Supporting implementation for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This stack-program composition and its bounds are auxiliary formalization results, not statements of the paper.

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_ParseCompare

namespace TwoAgentSched.TotalTotal.ParseCompare

open CookPvsNP ProjSchedTW.Complexity

theorem correct_and_total :
    (∀ (m n : ℕ) (tail : List BSym),
      ∃ (steps : ℕ) (left right result : List BSym),
        steps ≤ 3 * m.bits.length + 3 * n.bits.length +
          3 * min m.bits.length n.bits.length + 21 ∧
        parseCompare.Exec (store5 (encNat m ++ (encNat n ++ tail)) [] [] [] [.sep])
          (store5 tail left right [.one, .one, .one, .one] result) steps ∧
        (result.head? = some .zero ↔ m < n)) ∧
    (∀ input : List BSym, ∃ (out : Fin 5 → List BSym) (steps : ℕ),
      parseCompare.Exec (store5 input [] [] [] [.sep]) out steps ∧
        steps ≤ 9 * input.length + 21) := by sorry

end TwoAgentSched.TotalTotal.ParseCompare
