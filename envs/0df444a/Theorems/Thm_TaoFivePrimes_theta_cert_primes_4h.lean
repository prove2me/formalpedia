-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4h
-- name    : TaoFivePrimes.theta_cert_primes_4h
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:27.83268+00:00
-- url     : https://prove2.me/theorems/936b48a1-75e6-41fa-9dcf-56fa2cb81854
-- title:
--   theta cert primes 4h
-- statement:
--   Primality table (fine sub-chunk 4h): the primes $p$ with $1366 \le p \le 1420$ are exactly the 5 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4h : (Finset.Icc 1366 1420).filter Nat.Prime = ({ 1367, 1373, 1381, 1399, 1409 } : Finset ℕ) := by sorry
