-- Prove2me | Theorems.Thm_PolyEulerFlow_lemma_27
-- name    : PolyEulerFlow.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:19:26.740891+00:00
-- url     : https://prove2.me/theorems/84320bae-ec00-42b9-8329-39cd676a3b46
-- title:
--   Lemma 27 — weighted-grid estimates
-- statement:
--   Let $(\eta_k)$ be steps with $0<\eta_k\le1$, let $t_k=\sum_{i<k}\eta_i$ (so $t_{k+1}-t_k=\eta_k$), and let $m<n$. Then for every $b>0$
--   $$\sum_{k=m}^{n-1}\eta_ke^{-b(t_k-t_m)}\le\frac{e^b}{b},\tag{22}$$
--   $$\sum_{k=m}^{n-1}\eta_ke^{b(t_k-t_m)}\le\frac{e^{b(t_n-t_m)}-1}{b},\tag{23}$$
--   and for $0<\lambda<a$
--   $$\sum_{k=m}^{n-1}\eta_ke^{-\lambda(t_n-t_{k+1})}e^{-a(t_k-t_m)}\le\frac{e^a}{a-\lambda}e^{-\lambda(t_n-t_m)}.\tag{24}$$
--   Moreover, for $0<\lambda\le1$, $\prod_{k=m}^{n-1}(1-\lambda\eta_k)\le e^{-\lambda(t_n-t_m)}$, and for $\lambda>-1$, $\prod_{k=m}^{n-1}(1+\lambda\eta_k)\ge(1+\lambda)^{t_n-t_m}$.
--
--   These estimates replace integrals by weighted sums on an arbitrary grid with cells of width at most one, without any lower bound on the steps; they are what makes the clock and cycle estimates uniform in the mesh.
--
--   Differences from the source:
--   - generalization: products of 1 + λη_k are at least (1 + λ)^{t_n − t_m} (no range of λ printed) → for every λ > −1; reason: the page's context is λ ≥ 0 (Corollary 39, p.34); λ > −1 is where (1 + λ)^{t} is defined, and the bound holds there by concavity of log
--   - encoding: grid times with t_{k+1} − t_k = η_k → t_k = Σ_{i<k} η_i; reason: only differences of grid times occur
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), Lemma 27, p.28 (PDF 30)

import Mathlib
import Definitions.Def_PolyEulerFlow_eulerOrbit

namespace PolyEulerFlow

/-- **Lemma 27 (Weighted-grid estimates)**, p.28 (PDF 30). Bournez, One Polynomial Field for Every Euler Step and the Flow
(manuscript, sha256 c4e01b2b…).

Let `η_k ∈ (0, 1]`, `t_k = Σ_{i<k} η_i`, and `m < n`. Then (22) for `b > 0`; (23) for `b > 0`; (24) for `0 < λ < a`; products of
`1 - λη_k` for `0 < λ ≤ 1` are at most `e^{-λ(t_n - t_m)}`; and products of `1 + λη_k` are at least `(1 + λ)^{t_n - t_m}`.

**Formalization Note** The grid times are `t_k = physTime η k`; only differences of grid times occur, so the origin is immaterial.
The page prints no range of `λ` for the last product; it is stated for every `λ > -1`, where `(1 + λ)^{t}` is defined. -/
theorem lemma_27 (η : ℕ → ℝ) (hη : ∀ k, 0 < η k ∧ η k ≤ 1) (m n : ℕ) (hmn : m < n) :
    let t := physTime η
    (∀ b : ℝ, 0 < b →
      ∑ k ∈ Finset.Ico m n, η k * Real.exp (-b * (t k - t m)) ≤ Real.exp b / b) ∧
    (∀ b : ℝ, 0 < b →
      ∑ k ∈ Finset.Ico m n, η k * Real.exp (b * (t k - t m)) ≤ (Real.exp (b * (t n - t m)) - 1) / b) ∧
    (∀ lam a : ℝ, 0 < lam → lam < a →
      ∑ k ∈ Finset.Ico m n, η k * Real.exp (-lam * (t n - t (k + 1))) * Real.exp (-a * (t k - t m))
        ≤ Real.exp a / (a - lam) * Real.exp (-lam * (t n - t m))) ∧
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      ∏ k ∈ Finset.Ico m n, (1 - lam * η k) ≤ Real.exp (-lam * (t n - t m))) ∧
    (∀ lam : ℝ, -1 < lam →
      (1 + lam) ^ (t n - t m) ≤ ∏ k ∈ Finset.Ico m n, (1 + lam * η k)) := by sorry

end PolyEulerFlow
