-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4a
-- name    : TaoFivePrimes.theta_cert_primes_4a
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:14.99895+00:00
-- url     : https://prove2.me/theorems/45a60698-cdad-4200-a376-1b40f5b96a9f
-- title:
--   theta cert primes 4a
-- statement:
--   Primality table (fine sub-chunk 4a): the primes $p$ with $978 \le p \le 1033$ are exactly the 9 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4a : (Finset.Icc 978 1033).filter Nat.Prime = ({ 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033 } : Finset ℕ) := by sorry
