-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_weighted_sifted_bound
-- name    : PrimePairSieve_reciprocal_weighted_sifted_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T18:37:29.36435+00:00
-- url     : https://prove2.me/theorems/57f1cac9-90a4-4516-b34c-51479a521ff2
-- title:
--   A reciprocal weighted bound for the prime-pair sifted set
-- statement:
--   Let N,d be nonnegative integers with d even, and let z≥1 be real. Let Q be a finite set of positive squarefree integers q≤z containing 1. Let A⊆{0,…,N−1} and suppose that for every q∈Q, every prime p dividing q, and every n∈A, p does not divide n(n+d). Put
--   $$g_d(q)=\prod_{p\mid q}\begin{cases}1/(p-1),&p\mid d,\\2/(p-2),&p\nmid d.\end{cases}$$
--   Then
--   $$|A|\le\left(\sum_{q\in Q}\frac{g_d(q)}{N+16qz}\right)^{-1}.$$
--   This connects primitive Fourier lower energy to the nonuniform large sieve: reduced unit fractions have exact denominator q, are distinct across moduli, and have individual spacing at least 1/(qz). The q=1 term makes the denominator strictly positive. No absolute remainder term is assumed or dropped. Empty A, N=0, and d=0 are allowed.
--
--   Formalization Note: Q is a finset of positive natural numbers; the product is over the actual prime factors of q. All Fourier and analytic hypotheses have been discharged in the proof. The constant 16 is nonsharp. Quantitative lower bounds for the displayed denominator and conversion to an all-range prime-pair counting theorem remain separate obligations.
-- source:
--   Finite-Fourier upper-bound sieve, combining the accepted nonuniform large sieve https://prove2.me/theorems/ee72dd79-89b1-4fab-8700-1074eec4cacc with the accepted squarefree primitive Fourier energy https://prove2.me/theorems/9e02419f-6b64-4e1f-bafa-93f2120d65e4. Intended consumer: https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385. Known mathematics; this records a connected formal bound, not a novelty claim or completion of the all-range prime-pair mission.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.PNat.Basic
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve_reciprocal_weighted_sifted_bound
    (Q : Finset ℕ+) (h1 : 1 ∈ Q) (N d : ℕ) (z : ℝ) (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Squarefree (q : ℕ) ∧ ((q : ℕ) : ℝ) ≤ z)
    (hd : 2 ∣ d) (A : Finset ℕ) (hAN : A ⊆ Finset.range N)
    (hA : ∀ q ∈ Q, ∀ n ∈ A, ∀ p ∈ (q : ℕ).primeFactors, ¬ p ∣ n*(n+d)) :
    (A.card : ℝ) ≤ (∑ q ∈ Q,
      (∏ p ∈ (q : ℕ).primeFactors,
        if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) /
      ((N : ℝ)+16*((q : ℕ) : ℝ)*z))⁻¹ := by sorry
