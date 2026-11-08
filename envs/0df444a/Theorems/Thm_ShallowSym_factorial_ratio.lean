-- Prove2me | Theorems.Thm_ShallowSym_factorial_ratio
-- name    : ShallowSym.factorial_ratio
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:58:37.717084+00:00
-- url     : https://prove2.me/theorems/ae68d0b4-0245-458f-b772-aa5393d63600
-- title:
--   $k!/k^{k-1}\ge e^{-k}$
-- statement:
--   For every integer $k\ge 1$,
--
--   $$\frac{k!}{k^{k-1}} \ \ge\ e^{-k}.$$
--
--   This lower-bounds the probability that a random test with modulus $k$ passes at a fixed valid input.
--
--   Differences from the source:
--   - encoding: k!/k^{k−1} ≥ e^{−k}, no range stated → k ≥ 1; reason: k is a number of blocks; at k = 0 the quantity k^{k−1} = 0^{−1} is undefined, so the condition only excludes an undefined case
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §3 'Coverage with random tests', p.9

import Mathlib

namespace ShallowSym

/-- §3 "Coverage with random tests", p.9. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"Thus, the probability that a random test covers a valid x is k!/k^{k−1} ≥ e^{−k} by Stirling’s
approximation (or if you prefer, the Taylor series for e^x at x = k)."

For every integer `k ≥ 1`: `k!/k^{k−1} ≥ e^{−k}`.

**Formalization Note.** `k` is a number of blocks, so `k ≥ 1`; `k − 1` is a natural exponent. -/
theorem factorial_ratio (k : ℕ) (hk : 1 ≤ k) :
    Real.exp (-(k : ℝ)) ≤ (k.factorial : ℝ) / (k : ℝ) ^ (k - 1) := by sorry

end ShallowSym
