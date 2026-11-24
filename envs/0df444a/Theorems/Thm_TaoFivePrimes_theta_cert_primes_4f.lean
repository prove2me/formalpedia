-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4f
-- name    : TaoFivePrimes.theta_cert_primes_4f
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:24.916492+00:00
-- url     : https://prove2.me/theorems/24a2c755-3a3f-4a4b-bdd9-29e0ce3b6b5d
-- title:
--   theta cert primes 4f
-- statement:
--   Primality table (fine sub-chunk 4f): the primes $p$ with $1256 \le p \le 1310$ are exactly the 10 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4f : (Finset.Icc 1256 1310).filter Nat.Prime = ({ 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307 } : Finset ℕ) := by sorry
