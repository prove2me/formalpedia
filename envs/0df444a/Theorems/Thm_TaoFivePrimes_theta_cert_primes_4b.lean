-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4b
-- name    : TaoFivePrimes.theta_cert_primes_4b
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:18.978451+00:00
-- url     : https://prove2.me/theorems/49687731-aa11-4c60-adc7-c0b1086d65b5
-- title:
--   theta cert primes 4b
-- statement:
--   Primality table (fine sub-chunk 4b): the primes $p$ with $1034 \le p \le 1088$ are exactly the 7 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4b : (Finset.Icc 1034 1088).filter Nat.Prime = ({ 1039, 1049, 1051, 1061, 1063, 1069, 1087 } : Finset ℕ) := by sorry
