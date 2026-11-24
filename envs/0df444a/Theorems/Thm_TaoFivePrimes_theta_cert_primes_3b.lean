-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_3b
-- name    : TaoFivePrimes.theta_cert_primes_3b
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:09.448221+00:00
-- url     : https://prove2.me/theorems/573a4c74-83ec-4dc6-8929-8eb49970b738
-- title:
--   theta cert primes 3b
-- statement:
--   Primality table (fine sub-chunk 3b): the primes $p$ with $696 \le p \le 789$ are exactly the 13 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_3b : (Finset.Icc 696 789).filter Nat.Prime = ({ 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787 } : Finset ℕ) := by sorry
