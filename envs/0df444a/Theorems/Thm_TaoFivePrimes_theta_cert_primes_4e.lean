-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4e
-- name    : TaoFivePrimes.theta_cert_primes_4e
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:21.147119+00:00
-- url     : https://prove2.me/theorems/f77bfb15-11ca-40a3-9dfe-38eacf98fc70
-- title:
--   theta cert primes 4e
-- statement:
--   Primality table (fine sub-chunk 4e): the primes $p$ with $1200 \le p \le 1255$ are exactly the 8 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4e : (Finset.Icc 1200 1255).filter Nat.Prime = ({ 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249 } : Finset ℕ) := by sorry
