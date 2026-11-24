-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4g
-- name    : TaoFivePrimes.theta_cert_primes_4g
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:28.310997+00:00
-- url     : https://prove2.me/theorems/28aacd99-a031-4a3c-a1ad-6c7c69c117d1
-- title:
--   theta cert primes 4g
-- statement:
--   Primality table (fine sub-chunk 4g): the primes $p$ with $1311 \le p \le 1365$ are exactly the 4 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4g : (Finset.Icc 1311 1365).filter Nat.Prime = ({ 1319, 1321, 1327, 1361 } : Finset ℕ) := by sorry
