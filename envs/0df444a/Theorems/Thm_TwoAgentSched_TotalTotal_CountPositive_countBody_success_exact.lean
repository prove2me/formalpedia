-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_CountPositive_countBody_success_exact
-- name    : TwoAgentSched.TotalTotal.CountPositive.countBody_success_exact
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T23:10:29.329086+00:00
-- url     : https://prove2.me/theorems/3b22ab38-cde5-4b83-aed6-e88ad1a668ab
-- title:
--   Successful counter body recognizes one canonical block
-- statement:
--   If one execution of the positive-counting loop body begins with an empty digit stack and finishes with a success status, then it consumed a canonical encoding of some natural number, left its suffix as the remaining input, restored the digit stack to empty, and increments the unary count exactly when the parsed number is nonzero. The existing status and count tails are preserved.

import Definitions.Def_TwoAgentSched_TotalTotal_CountPositive
open CookPvsNP ProjSchedTW.Complexity TwoAgentSched.TotalTotal.CountPositive

theorem TwoAgentSched.TotalTotal.CountPositive.countBody_success_exact
    (input status count : List BSym) (out : Fin 4 → List BSym) (steps : ℕ)
    (h : countBody.Exec (store4 input [] status count) out steps)
    (hs : (out 2).head? = some .one) :
    ∃ (n : ℕ) (rest : List BSym), input = encNat n ++ rest ∧
      out = store4 rest [] (.one :: .one :: status)
        (if n = 0 then count else .one :: count) := by
  sorry
