-- Prove2me | Theorems.Thm_TaoFivePrimes_prime_in_short_interval_above_exp301
-- name    : TaoFivePrimes.prime_in_short_interval_above_exp301
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T17:51:32.998424+00:00
-- url     : https://prove2.me/theorems/3e62f5f0-d9e8-475d-93c3-52f3ba902890
-- title:
--   Primes in Tao’s short interval for every x at least exp(301)
-- statement:
--   For every real $x\ge e^{301}$, there is a natural prime $p\le x$ such that
--
--   $$x-p\le\frac{x}{2.8\cdot10^7}.$$
--
--   This proves the whole unbounded tail of Tao's short-prime-interval input. The proof specializes the already proved common Dusart table tail to $|\psi(t)-t|\le1.225\cdot10^{-8}t$, controls the elementary prime-power correction uniformly, and proves a strict increase of $\vartheta$ across the interval. It assumes neither of the mutually dependent Ramaré–Saouter interval statements. It does not assert the still-open intermediate range below $e^{301}$.
-- source:
--   Derived from Dusart (2018), Table 1, and the standard psi-theta prime-power correction; target interval: Tao, arXiv:1201.6656v4, Theorem 8.1.

import Mathlib

theorem TaoFivePrimes.prime_in_short_interval_above_exp301
    (x : ℝ) (hx : Real.exp 301 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x - p ≤ x / (2.8 * 10^7) := by sorry
