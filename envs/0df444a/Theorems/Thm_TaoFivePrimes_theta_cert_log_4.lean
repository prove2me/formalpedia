-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_log_4
-- name    : TaoFivePrimes.theta_cert_log_4
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:18:59.092866+00:00
-- url     : https://prove2.me/theorems/5238e850-7d77-4701-9950-606a2bdfb884
-- title:
--   theta cert log 4
-- statement:
--   Logarithmic table, fourth chunk: for every prime $p$ in the fourth block of primes $\le 1420$, $\lfloor 10^4 \log p\rfloor < 10^4 \log p$.
--
--   Same certified exponential-bound argument as the first chunk, for the 58 primes of the fourth chunk (the largest primes near 1400).
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_log_4 (p : ℕ) (hp : p ∈ plist4) : ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by sorry
