-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_CountPositive_success_exact
-- name    : TwoAgentSched.TotalTotal.CountPositive.success_exact
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T23:07:21.629583+00:00
-- url     : https://prove2.me/theorems/ae926549-375b-4cdc-aeec-3907469e731c
-- title:
--   Successful positive-count scans characterize canonical input
-- statement:
--   Suppose the fixed positive-count program starts with an arbitrary input and a success marker, terminates with an empty input stack, and its final status still indicates success. Then the original input is a canonical concatenation of encoded natural numbers, and the output counter contains exactly one unary symbol for each nonzero number. This is a converse needed for rejection of malformed encodings.

import Definitions.Def_TwoAgentSched_TotalTotal_CountPositive
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.CountPositive

theorem TwoAgentSched.TotalTotal.CountPositive.success_exact
    (input : List BSym) (out : Fin 4 → List BSym) (steps : ℕ)
    (h : countPositive.Exec (store4 input [] [.one] []) out steps)
    (hs : (out 2).head? = some .one) (he : out 0 = []) :
    ∃ xs : List ℕ, input = encNats xs ∧
      out 3 = List.replicate (xs.filter (fun x => x ≠ 0)).length .one := by
  sorry
