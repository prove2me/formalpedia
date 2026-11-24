-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_3a
-- name    : TaoFivePrimes.theta_cert_primes_3a
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T13:00:06.708276+00:00
-- url     : https://prove2.me/theorems/28830a29-0f9b-4d72-8a0c-896dc4999282
-- title:
--   theta cert primes 3a
-- statement:
--   Primality table (fine sub-chunk 3a): the primes $p$ with $602 \le p \le 695$ are exactly the 15 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_3a : (Finset.Icc 602 695).filter Nat.Prime = ({ 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691 } : Finset ℕ) := by sorry
