-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log
-- name    : TaoFivePrimes.theta_cert_clbZ_le_log
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:00:54.82279+00:00
-- url     : https://prove2.me/theorems/bfd735c4-23e5-4b29-88de-6388d62525f6
-- title:
--   theta cert clbZ le log
-- statement:
--   The complete logarithmic table: for every prime $p \le 1420$, $\lfloor 10^4 \log p\rfloor \le 10^4 \log p$.
--
--   Union of the four chunk bounds.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_log_1
import Theorems.Thm_TaoFivePrimes_theta_cert_log_2
import Theorems.Thm_TaoFivePrimes_theta_cert_log_3
import Theorems.Thm_TaoFivePrimes_theta_cert_log_4

namespace TaoFivePrimes
theorem theta_cert_clbZ_le_log (p : ℕ) (hp : p ∈ plist) : ((clbZ p : ℕ) : ℝ) ≤ Real.log p * 10 ^ 4 := by sorry
