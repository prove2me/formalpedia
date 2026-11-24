-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_log_2
-- name    : TaoFivePrimes.theta_cert_log_2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:19:01.180064+00:00
-- url     : https://prove2.me/theorems/7703b6cc-7563-43a5-9314-5d0ca27a1ef6
-- title:
--   theta cert log 2
-- statement:
--   Logarithmic table, second chunk: for every prime $p$ in the second block of primes $\le 1420$, $\lfloor 10^4 \log p\rfloor < 10^4 \log p$.
--
--   Same certified exponential-bound argument as the first chunk, for the 55 primes of the second chunk.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_log_2 (p : ℕ) (hp : p ∈ plist2) : ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by sorry
