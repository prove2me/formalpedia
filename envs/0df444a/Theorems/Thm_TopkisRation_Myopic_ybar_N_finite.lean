-- Prove2me | Theorems.Thm_TopkisRation_Myopic_ybar_N_finite
-- name    : TopkisRation.Myopic.ybar_N_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:35.168753+00:00
-- url     : https://prove2.me/theorems/c5a65218-7624-4e52-af58-adff39360ce3
-- title:
--   Theorem 4 proof, p. 175 — the final myopic level is finite
-- statement:
--   Suppose the terminal salvage revenue equals the terminal procurement cost, $v=c_{N+1}$, and there is at least one ordering period. Then the final-period myopic cost $g^N$ has a nonnegative minimizer. Consequently every level $\bar y_N$ chosen by the paper's rule is finite:
--
--   $$\bar y_N<+\infty.$$
--
--   This is the base case of the backward comparison that proves Theorem 4.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 175, proof of Theorem 4, first sentence

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- Theorem 4 proof, p. 175: the last myopic level is finite. -/
theorem ybar_N_finite (Q : MultiModel n) (hQ : Q.Standing)
    (hv : Q.v = Q.c (Q.N + 1)) (hN : 1 ≤ Q.N) :
    ∀ y : WithTop ℝ, IsMyopicLevel (Q.gmyopic Q.N) y → y ≠ ⊤ := by sorry

end TopkisRation.Myopic
