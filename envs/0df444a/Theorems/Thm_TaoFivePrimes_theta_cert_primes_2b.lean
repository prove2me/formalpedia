-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_2b
-- name    : TaoFivePrimes.theta_cert_primes_2b
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:59:59.16053+00:00
-- url     : https://prove2.me/theorems/931c5729-cb71-42ab-a824-8021a7d6903f
-- title:
--   theta cert primes 2b
-- statement:
--   Primality table (fine sub-chunk 2b): the primes $p$ with $430 \le p \le 601$ are exactly the 28 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_2b : (Finset.Icc 430 601).filter Nat.Prime = ({ 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601 } : Finset ℕ) := by sorry
