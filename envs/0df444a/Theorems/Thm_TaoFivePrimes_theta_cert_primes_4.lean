-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4
-- name    : TaoFivePrimes.theta_cert_primes_4
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:54:46.188542+00:00
-- url     : https://prove2.me/theorems/ba1af5d1-634b-4bfa-9f0b-9231af4a6ca2
-- title:
--   theta cert primes 4
-- statement:
--   Primality table, chunk 4: the primes $p$ with $978 \le p \le 1420$ are exactly the 58 entries of the explicit table ``plist4``.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4 : (Finset.Icc 978 1420).filter Nat.Prime = plist4 := by sorry
