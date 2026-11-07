-- Prove2me | Theorems.Thm_ReadTwiceCount_marginal_le_half
-- name    : ReadTwiceCount.marginal_le_half
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:53.574959+00:00
-- url     : https://prove2.me/theorems/0f7048e5-80ee-417e-bbbf-5d7cea4016c4
-- title:
--   §2 (2) — the marginal of a dangling query satisfies $0\le p(H,h)\le 1/2$
-- statement:
--   Let $H$ be a satisfiable read-twice normalized state and $h$ a dangling query of $H$. Then
--   $$0\le p(H,h)\le\frac12,$$
--   and if the variable of $h$ is free (with either sign of $h$), $p(H,h)=\frac12$.
--
--   This is the first bound on marginals; it gives $y(H,h)\ge1$ for positive queries and is the base of the coordinate $y=1/p-1$.
--
--   Differences from the source: none.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §2, display (2) and the paragraph after it, p.3

import Mathlib
import Definitions.Def_ReadTwiceCount_pFalse

namespace ReadTwiceCount

/-- **The marginal of a dangling query is at most 1/2** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §2,
after display (2), p.3): "If the variable is free, either sign may be queried and p(H, h) = 1/2. If
it occurs in one clause, flipping it from false to true maps satisfying assignments injectively to
satisfying assignments. Consequently 0 ≤ p(H, h) ≤ 1/2."

For a satisfiable read-twice normalized state `H` (the standing assumptions on states, §2, p.2)
and a dangling query `h`: `0 ≤ p(H, h) ≤ 1/2`, and `p(H, h) = 1/2`
when the variable of `h` is free (with either sign of `h`). -/
theorem marginal_le_half {M : ℕ} (H : Formula M) (h : Lit M) (hRT : ReadTwice H)
    (hN : Normalized H) (hD : IsDangling H h) (hZ : 0 < Z H) :
    0 ≤ pFalse H h ∧ pFalse H h ≤ 1 / 2 ∧ (H.occ h.1 = 0 → pFalse H h = 1 / 2) := by sorry

end ReadTwiceCount
