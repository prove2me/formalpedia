-- Prove2me | Theorems.Thm_ReadTwiceCount_parent_marginal
-- name    : ReadTwiceCount.parent_marginal
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:52.866697+00:00
-- url     : https://prove2.me/theorems/88d2e846-c491-45ff-9dfb-1ba495eb9b15
-- title:
--   §3 (5) — the parent marginal $p=(1-Q)/(2-Q)$, $y=1/(1-Q)$
-- statement:
--   Let $H$ be a read-twice normalized state and $h$ a positive dangling query of $H$ whose variable occurs, in the clause $v$, and let $Q$ be the probability, in $H-v$, that all other literals of $v$ are false. Then
--   $$p(H,h)=\frac{1-Q}{2-Q},\qquad y(H,h)=\frac{1}{1-Q}.$$
--
--   With the prefix product (4), this is the exact conditioned recurrence; substituting $p_i=1/(y_i+1)$ gives the descriptor (6).
--
--   Differences from the source:
--   - encoding: $Q$ as a proportion of the assignments of $H-v$ to the variables other than the queried variable → $Q$ as a proportion of the satisfying assignments of $H-v$ on the whole universe; reason: the queried variable does not occur in $H-v$, so including it doubles both counts and leaves the proportion unchanged
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §3, display (5), p.4

import Mathlib
import Definitions.Def_ReadTwiceCount_stateDesc

namespace ReadTwiceCount

/-- **The parent marginal (5)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §3, display (5), p.4): for a
positive dangling query `h` whose variable occurs, in a read-twice normalized state `H`, with `Q` the
probability in `H − v` that all other literals of its clause `v` are false,
`p = (1 − Q)/(2 − Q)` and `y = 1/(1 − Q)`. -/
theorem parent_marginal {M : ℕ} (H : Formula M) (h : Lit M) (hRT : ReadTwice H)
    (hN : Normalized H) (hD : IsDangling H h) (hP : IsPositive H h) (hocc : H.occ h.1 = 1) :
    pFalse H h = (1 - prefixQ H h) / (2 - prefixQ H h) ∧
      yCoord H h = 1 / (1 - prefixQ H h) := by sorry

end ReadTwiceCount
