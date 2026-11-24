-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primesLE_eq
-- name    : TaoFivePrimes.theta_cert_primesLE_eq
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:01:07.030142+00:00
-- url     : https://prove2.me/theorems/c6dadf7e-7b34-4e51-94c7-6eba83ffee97
-- title:
--   theta cert primesLE eq
-- statement:
--   Truncated prime lists: for every $n \le 1420$, Mathlib's `Nat.primesLE n` (the primes $\le n$) is the truncation of the explicit table `plist` to the entries $\le n$.
--
--   Immediate from the completeness of the table (previous theorem) and `Finset.filter_filter`.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq

namespace TaoFivePrimes
theorem theta_cert_primesLE_eq (n : ℕ) (hn : n ≤ 1420) : Nat.primesLE n = plist.filter (· ≤ n) := by sorry
