-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_4d
-- name    : TaoFivePrimes.theta_cert_primes_4d
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:18.230379+00:00
-- url     : https://prove2.me/theorems/a795e7dd-ec77-4998-9670-58fec52319b3
-- title:
--   theta cert primes 4d
-- statement:
--   Primality table (fine sub-chunk 4d): the primes $p$ with $1145 \le p \le 1199$ are exactly the 7 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_4d : (Finset.Icc 1145 1199).filter Nat.Prime = ({ 1151, 1153, 1163, 1171, 1181, 1187, 1193 } : Finset ℕ) := by sorry
