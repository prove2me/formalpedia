-- Prove2me | Theorems.Thm_PrimorialRange_bound_34129386_42496200
-- name    : PrimorialRange.bound_34129386_42496200
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T07:04:54.153546+00:00
-- url     : https://prove2.me/theorems/1f4b6d3d-1f97-4621-a9c4-382715461e3a
-- title:
--   Explicit primorial bound $n\# \cdot 25^n < 68^n$ for $34\,129\,386 < n \le 42\,496\,200$
-- statement:
--   Let $n\# = \prod_{p \le n,\, p\text{ prime}} p$ denote the primorial of a natural number $n$, and let $\theta(x) = \sum_{p \le x} \log p$ be the first Chebyshev function. For every natural number $n$ satisfying $34\,129\,386 < n \le 42\,496\,200$,
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
theorem bound_34129386_42496200 (n : ℕ) (hn : 34129386 < n) (hn' : n ≤ 42496200) :
    primorial n * 25 ^ n < 68 ^ n := by sorry
end PrimorialRange
