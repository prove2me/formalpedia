-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_log_3
-- name    : TaoFivePrimes.theta_cert_log_3
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:19:03.434727+00:00
-- url     : https://prove2.me/theorems/83998b66-8c64-4ec7-b058-f33a970a645b
-- title:
--   theta cert log 3
-- statement:
--   Logarithmic table, third chunk: for every prime $p$ in the third block of primes $\le 1420$, $\lfloor 10^4 \log p\rfloor < 10^4 \log p$.
--
--   Same certified exponential-bound argument as the first chunk, for the 55 primes of the third chunk.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_log_3 (p : ℕ) (hp : p ∈ plist3) : ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by sorry
