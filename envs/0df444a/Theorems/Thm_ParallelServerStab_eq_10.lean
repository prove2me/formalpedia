-- Prove2me | Theorems.Thm_ParallelServerStab_eq_10
-- name    : ParallelServerStab.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:55.56527+00:00
-- url     : https://prove2.me/theorems/4f89cb63-b435-4cce-a9b1-e1f29e800f1d
-- title:
--   Eq. (10) — $V_{cr}(p)<1$ if and only if $p>1-1/s$
-- statement:
--   Let $s\ge2$ be the number of servers and $p>0$. The critical value $V_{cr}(p)$ of (9) satisfies
--
--   $$
--   V_{cr}(p)<1 \iff p>1-\frac1s .
--   $$
--
--   So the bound of Theorem 2 is below the usual traffic condition $\rho<1$ exactly when the error probability exceeds $1-1/s$; for smaller $p$ Theorem 2 says nothing beyond $\rho<1$.
--
--   Differences from the source:
--   - reading: $s \ge 1$ servers in (9), $s$ servers in §3 → $s \ge 2$; reason: the model has $s \ge 2$ servers (§1, p. 1), $p_{p,2}=(1-p,p,0,\dots,0)$ needs two coordinates, and (9) divides by $p(s-1)$
--   - generalization: an error probability $p>0$ (so $p\le1$) → every real $p>0$; reason: the equivalence is algebraic; the source's range is contained
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, eq. (10), p.11 (with (9), p.11)

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr

namespace ParallelServerStab

/-- Eq. (10) (Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, eq. (10),
p. 11): for `s ≥ 2` servers and an error probability `p > 0`, the critical value of (9)
satisfies `V_cr(p) < 1` if and only if `p > 1 − 1/s`.

**Formalization Note.** `s ≥ 2` (the paper writes `s ≥ 1`, but (9) divides by `p(s − 1)`);
`p` is any positive real, not only `p ≤ 1`. -/
theorem eq_10 (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp : 0 < p) :
    Vcr s p < 1 ↔ 1 - 1 / (s : ℝ) < p := by sorry

end ParallelServerStab
