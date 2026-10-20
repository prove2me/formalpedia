-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_nearSubadditiveConvergence
-- name    : QAlgorithms.Papers.Independent.Information100.P69.nearSubadditiveConvergence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:13:14.04173+00:00
-- url     : https://prove2.me/theorems/7fd4980b-c65e-47cb-a9f3-ce0a6eb3d4f4
-- title:
--   Near-subadditive sequence convergence
-- statement:
--   Let $(a_n)$ be a real sequence and $C_0,C_1$ finite real constants with $0\le a_n\le C_0n+C_1$ for positive $n$. Let $F$ be nonnegative and nondecreasing on positive integers and satisfy $F(s)=O(s^{2/3}\log_2(s+1))$. If
--   $$a_{n+m}\le a_n+a_m+F(n+m)\qquad(n,m\ge1),$$
--   then there is a finite real $R$ such that
--   $$\lim_{n\to\infty}\frac{a_n}{n}=R.$$
--   This scalar convergence lemma requires the specified summably controlled remainder and has no channel hypotheses.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 41, Lemma 34

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 34, finite ordinary convergence for the specified summably controlled remainder;
no channel hypotheses; arXiv:2609.30762v1, PDF p.41. -/
theorem nearSubadditiveConvergence (a F : ℕ → ℝ) (C0 C1 : ℝ)
    (ha : ∀ n, 1 ≤ n → 0 ≤ a n ∧ a n ≤ C0*n+C1)
    (hsub : ∀ n m, 1 ≤ n → 1 ≤ m → a (n+m) ≤ a n+a m+F (n+m))
    (hF : ∀ n, 1 ≤ n → 0 ≤ F n)
    (hmono : ∀ n m, 1 ≤ n → n ≤ m → F n ≤ F m)
    (hbound : ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, ∀ n, 1 ≤ n → n0 ≤ n →
      F n ≤ K*(n:ℝ)^(2/3:ℝ)*Real.logb 2 ((n:ℝ)+1)) :
    ∃ R : ℝ, Tendsto (fun j : ℕ => a (j+1)/(j+1)) atTop (nhds R) := by sorry

end QAlgorithms.Papers.Independent.Information100.P69

end
