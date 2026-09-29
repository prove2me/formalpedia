-- Prove2me | Theorems.Thm_TaoFivePrimes_farey_rough_separation
-- name    : TaoFivePrimes.farey_rough_separation
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:54:38.279278+00:00
-- url     : https://prove2.me/theorems/e720e06f-039f-4c0b-a736-68f88bacc92c
-- title:
--   Tao Lemma 4.6 (proof): disjointness of the translated Farey systems
-- statement:
--   Let $Q,R$ be positive integers. Let $q_0,q_0'$ be positive integers at most $Q$, and let $q_1,q_1'$ be positive integers at most $R$ none of whose prime factors is at most $Q$. Let $a_0,a_0',a_1,a_1'$ be integers. If
--
--   $$\left\|\frac{a_0}{q_0}+\frac{a_1}{q_1}-\frac{a_0'}{q_0'}-\frac{a_1'}{q_1'}\right\|_{\mathbb R/\mathbb Z}<\frac{1}{Q^2R^2},$$
--
--   then $\dfrac{a_1}{q_1}=\dfrac{a_1'}{q_1'}$ in $\mathbb R/\mathbb Z$, that is, $q_1q_1'$ divides $a_1q_1'-a_1'q_1$. Here $\|t\|_{\mathbb R/\mathbb Z}$ is the distance from $t$ to the nearest integer.
--
--   This is the Farey-type separation that makes the translated major-arc systems disjoint. In the local $L^2$ estimate for smoothed prime exponential sums one takes the union $\Sigma$ of the intervals of radius $1/(2Q^2R^2)$ around the fractions $a_0/q_0$ with $q_0\le Q$, and translates it by the fractions $a_1/q_1$ with $q_1\le R$ coprime to the primorial $Q\sharp$; the statement above says that two such translates can only meet if their translation vectors already agree modulo $1$, which is what allows the translated copies to be summed against a single global $L^2$ bound.
--
--   The two mechanisms are: a nonzero rational with denominator at most $Q^2R^2$ is at distance at least $1/(Q^2R^2)$ from the integers, which forces the displayed difference to be an integer; and the rough denominators $q_1,q_1'$ are coprime to the smooth ones $q_0,q_0'$, which forces the rough part of that integer relation to be integral on its own.
--
--   **Formalization Note** The distance to the nearest integer is written as the existence of an integer $k$ with $|t-k|$ small, which for a distance below $1/2$ is the same condition. The conclusion is stated as the integer divisibility $q_1q_1'\mid a_1q_1'-a_1'q_1$, which is equivalent to $a_1/q_1-a_1'/q_1'\in\mathbb Z$ and avoids a second existential. Roughness of $q_1$ and $q_1'$ is stated primewise; the fractions are not assumed to be in lowest terms.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.6 (Local L^2 estimate), the final paragraph ('the sets Sigma + a_1/q_1 are disjoint up to measure zero sets')

import Mathlib

open Finset

theorem TaoFivePrimes.farey_rough_separation (Q R : ℕ)
    (q0 q0' q1 q1' : ℕ) (a0 a0' a1 a1' : ℤ)
    (hq0 : 0 < q0) (hq0Q : q0 ≤ Q) (hq0' : 0 < q0') (hq0'Q : q0' ≤ Q)
    (hq1 : 0 < q1) (hq1R : q1 ≤ R) (hq1' : 0 < q1') (hq1'R : q1' ≤ R)
    (hrough : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1)
    (hrough' : ∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q1')
    (hclose : ∃ k : ℤ,
      |((a0 : ℝ) / q0 + (a1 : ℝ) / q1 - (a0' : ℝ) / q0' - (a1' : ℝ) / q1') - (k : ℝ)|
        < 1 / ((Q : ℝ) ^ 2 * (R : ℝ) ^ 2)) :
    ((q1 : ℤ) * q1') ∣ (a1 * q1' - a1' * q1) := by sorry
