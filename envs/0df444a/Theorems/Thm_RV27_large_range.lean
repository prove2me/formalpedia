-- Prove2me | Theorems.Thm_RV27_large_range
-- name    : RV27.large_range
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T18:20:31.117623+00:00
-- url     : https://prove2.me/theorems/70bf9bef-685f-43a2-85ec-dfafa337403e
-- title:
--   Large range of the K = 27 Schnirelmann density bound: at least n/25 even numbers up to n are sums of two odd primes for log n ≥ 300
-- statement:
--   For every integer $n$ with $\log n \ge 300$, at least $n/25$ of the integers $0 \le s \le n$ are a sum $s = p + q$ of two odd primes:
--   $$\#\{0 \le s \le n : r(s) > 0\} \ \ge\ \frac{n}{25},$$
--   where $r(s)$ (`Schnir.r`) counts ordered pairs of odd primes $(p, q)$ with $p + q = s$.
--
--   This is the large-range part of the explicit Schnirelmann-density argument for $K = 27$ (every integer $> 1$ is a sum of at most 27 primes). It follows Riesel and Vaughan (1983), §§7–8: split $(h, 1002h]$, $h = \lfloor n/2004 \rfloor$, into $1000$ overlapping intervals $(kh, kh + 2h]$, weight each pair of primes from one interval by the truncated singular-series weight $w(m) = \prod_{p \mid m,\ 3 \le p \le E}(p-2)/(p-1)$, bound the weighted pair count from below with the Montgomery–Vaughan large sieve for primitive characters, and from above by $\#\{s \le n : r(s) > 0\}$ times the Siebert-type bound for one sum. Chebyshev's elementary bound $\psi(x) \ge 0.9212x - 5\log x$ replaces the Rosser–Schoenfeld prime number estimates, so no information on zeta zeros is used.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, §§7–8 (Lemmas 9–15), with Chebyshev's bound in place of Rosser–Schoenfeld. Uses platform nodes RV27.interval_goldbach_bound, RV27.interval_pair_weight_lower and PrimePairSieve.sieve_constants_certificate.

import Mathlib
import Definitions.Def_Schnir_defs

theorem RV27.large_range (n : ℕ) (hn : Real.exp 300 ≤ (n : ℝ)) :
    (n : ℝ) / 25 ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := by sorry
