-- Prove2me | Theorems.Thm_RV27_interval_reciprocal_weighted_sifted_bound
-- name    : RV27.interval_reciprocal_weighted_sifted_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T14:36:25.586493+00:00
-- url     : https://prove2.me/theorems/d421de42-95aa-4ab8-8b79-a665838148be
-- title:
--   Weighted large-sieve bound for prime-pair sifted sets in an arbitrary interval
-- statement:
--   Let $z \ge 1$, let $\mathcal Q$ be a finite set of squarefree positive integers $q \le z$ containing $1$, let $d$ be even, and let $A$ be a finite set of integers contained in an interval $[M, M+N)$ of length $N$. Suppose that for every $q \in \mathcal Q$, every $n \in A$ and every prime $p \mid q$ we have $p \nmid n(n+d)$. Then
--   $$|A| \le \Big(\sum_{q \in \mathcal Q} \frac{h_d(q)}{N + 16 q z}\Big)^{-1}, \qquad h_d(q) = \prod_{p \mid q} \begin{cases} \frac{1}{p-1} & p \mid d,\\ \frac{2}{p-2} & p \nmid d.\end{cases}$$
--   This is the interval form of the platform theorem `PrimePairSieve_reciprocal_weighted_sifted_bound` (there $A \subseteq [0,N)$); it is the Montgomery–Vaughan weighted large sieve for sets sifted by the two residue classes $0$ and $-d$, as used for Lemma 5 of Riesel–Vaughan.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, Lemma 5 and §7 (Lemma 9, sieve on short intervals); H. L. Montgomery and R. C. Vaughan, The large sieve, Mathematika 20 (1973) 119–134, Theorem 1. Interval generalisation of platform node PrimePairSieve_reciprocal_weighted_sifted_bound (57f1cac9).

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.PNat.Basic
open scoped BigOperators
set_option autoImplicit false

theorem RV27.interval_reciprocal_weighted_sifted_bound
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (M N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.Ico M (M + N))
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹ := by sorry
