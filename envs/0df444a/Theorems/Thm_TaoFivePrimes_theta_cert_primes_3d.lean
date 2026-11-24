-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_3d
-- name    : TaoFivePrimes.theta_cert_primes_3d
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:16.346757+00:00
-- url     : https://prove2.me/theorems/98bdbaf6-afd6-4b45-90bb-c7fe5c8a1739
-- title:
--   theta cert primes 3d
-- statement:
--   Primality table (fine sub-chunk 3d): the primes $p$ with $884 \le p \le 977$ are exactly the 12 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_3d : (Finset.Icc 884 977).filter Nat.Prime = ({ 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977 } : Finset ℕ) := by sorry
