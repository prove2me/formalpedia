-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_3c
-- name    : TaoFivePrimes.theta_cert_primes_3c
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:12.739288+00:00
-- url     : https://prove2.me/theorems/6a50c33f-dbdb-4805-9be4-4189e6443b7b
-- title:
--   theta cert primes 3c
-- statement:
--   Primality table (fine sub-chunk 3c): the primes $p$ with $790 \le p \le 883$ are exactly the 15 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_3c : (Finset.Icc 790 883).filter Nat.Prime = ({ 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883 } : Finset ℕ) := by sorry
