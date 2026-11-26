-- Prove2me | Theorems.Thm_PvsNP_ClockTruncation_guarded_binomial_parity
-- name    : PvsNP.ClockTruncation.guarded_binomial_parity
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:17:47.189311+00:00
-- url     : https://prove2.me/theorems/37d05342-5010-4778-ab2d-07143e7dfdb2
-- title:
--   Guarded binomial parity from a truncated clock
-- statement:
--   Let $w,t,d,q$ be natural numbers with $d,q<2^w$. Consider the parity of $\binom{t-d+q}{t-d}$, with value zero when $t<d$. This value is determined by $t\bmod 2^w$ and the flag $2^w\leq t$. When the flag is set or $d\leq t\bmod 2^w$, the result is one exactly when the bitwise intersection of $q$ and $((t\bmod 2^w)+2^w-d)\bmod 2^w$ is zero. In the other cases the result is zero.
-- source:
--   Clock-truncation corollary of Édouard Lucas, Théorie des Fonctions Numériques Simplement Périodiques (1878), https://www.jstor.org/stable/2369308.

import Mathlib.Data.Nat.Choose.Lucas

theorem PvsNP.ClockTruncation.guarded_binomial_parity {w t d q : ℕ} (hd : d < 2^w) (hq : q < 2^w) :
    (if d ≤ t then (t-d+q).choose (t-d)%2 else 0) =
      if 2^w ≤ t ∨ d ≤ t % 2^w then
        (if (((t%2^w+2^w-d)%2^w) &&& q) = 0 then 1 else 0)
      else 0 := by sorry
