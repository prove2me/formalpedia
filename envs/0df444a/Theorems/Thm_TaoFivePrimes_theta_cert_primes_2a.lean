-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_primes_2a
-- name    : TaoFivePrimes.theta_cert_primes_2a
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:59:57.127062+00:00
-- url     : https://prove2.me/theorems/2c6777ad-566b-4685-83d8-bd51e7fddd5b
-- title:
--   theta cert primes 2a
-- statement:
--   Primality table (fine sub-chunk 2a): the primes $p$ with $258 \le p \le 429$ are exactly the 27 entries of the displayed table.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_primes_2a : (Finset.Icc 258 429).filter Nat.Prime = ({ 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421 } : Finset ℕ) := by sorry
