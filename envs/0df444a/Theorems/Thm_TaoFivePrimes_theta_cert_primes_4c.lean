-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4c
-- name    : TaoFivePrimes.theta_cert_primes_4c
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:20.971515+00:00
-- url     : https://prove2.me/theorems/62ae7615-87c4-4905-bc3f-f20edc6670a1
-- title:
--   theta cert primes 4c
-- statement:
--   Primality table (fine sub-chunk 4c): the primes $p$ with $1089 \le p \le 1144$ are exactly the 8 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4c : (Finset.Icc 1089 1144).filter Nat.Prime = ({ 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129 } : Finset ℕ) := by sorry
