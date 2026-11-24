-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_log_1
-- name    : TaoFivePrimes.theta_cert_log_1
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:18:54.829935+00:00
-- url     : https://prove2.me/theorems/0b038e0e-c6a7-4b40-9958-cb885040229d
-- title:
--   theta cert log 1
-- statement:
--   Logarithmic table, first chunk: for every prime $p$ in the first block of primes $\le 1420$, the integer $\lfloor 10^4 \log p\rfloor$ (stored in `clbZ`) is a strict lower bound for $10^4 \log p$.
--
--   Each of the 55 primes is checked by the exponential lower bound $e^{m+f} \le e^m (\sum_{k<12} f^k/k! + f^{12}\cdot 13/(12!\cdot 12)) \le 2.7182818286^m \cdot (\ldots) < p$ with $m = \lfloor \log p\rfloor/10^4$ and $f = (\log p - m)/10^4$, so that $m + f < \log p$ (Mathlib's `Real.exp_bound'`).
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_log_1 (p : ℕ) (hp : p ∈ plist1) : ((clbZ p : ℕ) : ℝ) < Real.log p * 10 ^ 4 := by sorry
