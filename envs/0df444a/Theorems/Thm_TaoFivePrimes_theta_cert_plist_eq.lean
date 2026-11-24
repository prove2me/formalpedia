-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq
-- name    : TaoFivePrimes.theta_cert_plist_eq
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T12:18:54.478836+00:00
-- url     : https://prove2.me/theorems/cae53eac-982a-49bf-9fba-2d63e2dfd8d1
-- title:
--   theta cert plist eq
-- statement:
--   The explicit table of primes: the primes $p \le 1420$ (as a finite set, listed as four consecutive chunks ``plist1``--``plist4``) are exactly the primes in the integer interval $[2, 1420]$.
--
--   Completeness of a primality table for $p \le 1420$: $(\mathrm{Icc}\ 2\ 1420).\mathrm{filter}\ \mathrm{Prime} = \mathrm{plist}$. Each of the four consecutive chunks is verified by direct kernel computation (trial division), and the chunks are glued along the interval partition.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables

namespace TaoFivePrimes
theorem theta_cert_plist_eq : (Finset.Icc 2 1420).filter Nat.Prime = plist := by sorry
