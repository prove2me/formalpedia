-- Prove2me | Theorems.Thm_TaoFivePrimes_tao_totient_cert_nth_prime_eq
-- name    : TaoFivePrimes.tao_totient_cert_nth_prime_eq
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:45:06.42745+00:00
-- url     : https://prove2.me/theorems/c4199999-74ce-4811-97e7-67d2083fe21c
-- title:
--   The certificate prime table agrees with the sequence of primes
-- statement:
--   Let $p_1 < p_2 < \cdots$ denote the primes in increasing order, so that $p_{i+1}$ is Mathlib's zero-indexed prime sequence `Nat.nth Nat.Prime i`. The certificate table `ptab` lists the first 66 primes: $\mathrm{ptab}(0)=2$, $\mathrm{ptab}(1)=3$, $\ldots$, $\mathrm{ptab}(65)=317$.
--
--   The theorem states that the table agrees with the prime sequence:
--   $$ \mathrm{ptab}(i) \;=\; p_{i+1} \qquad (0 \le i < 66). $$
--
--   This identification lets the finite verification of the Rosser--Schoenfeld totient bound substitute the explicit numerical table `ptab` for the abstract sequence $p_{i+1}$ whenever the first 66 primes occur, which is what makes the numerical inequalities checkable by computation.
--
--   *Formalization note.* In Lean the statement is `Nat.nth Nat.Prime i = ptab i` for `i < 66`; the bound `hi : i < 66` is what removes the default value of the table outside its range.
-- source:
--   Input data for the finite Rosser--Schoenfeld (1962) totient verification formalized in this project. The values are the primes below 320, as tabulated in J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Section 5.

import Mathlib.Data.Nat.Prime.Nth
import Definitions.Def_TaoFivePrimes_totient_cert_tables

namespace TaoFivePrimes

theorem tao_totient_cert_nth_prime_eq (i : ℕ) (hi : i < 66) :
    Nat.nth Nat.Prime i = ptab i := by sorry

end TaoFivePrimes
