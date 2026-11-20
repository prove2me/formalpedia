-- Prove2me | Theorems.Thm_PrimorialRange_bound_42496200_52597756
-- name    : PrimorialRange.bound_42496200_52597756
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T07:04:57.18224+00:00
-- url     : https://prove2.me/theorems/0f11d835-fdcf-4574-b3de-575c5ff5c61f
-- title:
--   Explicit primorial bound $n\# \cdot 25^n < 68^n$ for $42\,496\,200 < n \le 52\,597\,756$
-- statement:
--   Let $n\# = \prod_{p \le n,\, p\text{ prime}} p$ denote the primorial of a natural number $n$, and let $\theta(x) = \sum_{p \le x} \log p$ be the first Chebyshev function. For every natural number $n$ satisfying $42\,496\,200 < n \le 52\,597\,756$,
--
--   $$n\# \cdot 25^n < 68^n,$$
--
--   or equivalently $\theta(n) < n\log(68/25)$ throughout this range.
--
--   This finite-range primorial inequality forms one of eight consecutive subranges partitioning $(3.2 \cdot 10^7, 10^8]$, used to assemble the explicit Chebyshev bound needed in the ternary Goldbach estimates of Liu and Wang (2002).
-- source:
--   L. Schoenfeld, Sharper bounds for the Chebyshev functions theta(x) and psi(x). II, Math. Comp. 30 (1976), 337-360, p. 356, display 5.1*; M.-C. Liu and T. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105 (2002), 133-175.

import Mathlib.NumberTheory.Primorial

namespace PrimorialRange
theorem bound_42496200_52597756 (n : ℕ) (hn : 42496200 < n) (hn' : n ≤ 52597756) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end PrimorialRange
