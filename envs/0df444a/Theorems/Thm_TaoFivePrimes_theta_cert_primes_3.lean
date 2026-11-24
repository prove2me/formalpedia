-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_3
-- name    : TaoFivePrimes.theta_cert_primes_3
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:54:37.433412+00:00
-- url     : https://prove2.me/theorems/ab094b55-1c7d-4b83-9a93-c97f7ec96c96
-- title:
--   theta cert primes 3
-- statement:
--   Primality table, chunk 3: the primes $p$ with $602 \le p \le 977$ are exactly the 55 entries of the explicit table ``plist3``.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_3 : (Finset.Icc 602 977).filter Nat.Prime = plist3 := by sorry
