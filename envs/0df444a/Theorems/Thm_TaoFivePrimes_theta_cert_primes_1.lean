-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_1
-- name    : TaoFivePrimes.theta_cert_primes_1
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:54:39.879811+00:00
-- url     : https://prove2.me/theorems/e4f17102-d063-4c6f-891f-c4b77be8413b
-- title:
--   theta cert primes 1
-- statement:
--   Primality table, chunk 1: the primes $p$ with $2 \le p \le 257$ are exactly the 55 entries of the explicit table ``plist1``.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_1 : (Finset.Icc 2 257).filter Nat.Prime = plist1 := by sorry
