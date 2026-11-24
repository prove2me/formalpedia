-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_2
-- name    : TaoFivePrimes.theta_cert_primes_2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:54:41.897757+00:00
-- url     : https://prove2.me/theorems/1fbdf723-113d-420d-a4b7-7be38eee763c
-- title:
--   theta cert primes 2
-- statement:
--   Primality table, chunk 2: the primes $p$ with $258 \le p \le 601$ are exactly the 55 entries of the explicit table ``plist2``.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_2 : (Finset.Icc 258 601).filter Nat.Prime = plist2 := by sorry
