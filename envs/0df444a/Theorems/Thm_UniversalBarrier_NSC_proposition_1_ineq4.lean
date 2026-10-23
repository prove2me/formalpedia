-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_proposition_1_ineq4
-- name    : UniversalBarrier.NSC.proposition_1_ineq4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:55.362075+00:00
-- url     : https://prove2.me/theorems/a0e5cee1-ef00-4066-922e-220427f830fe
-- title:
--   Proposition 1, inequality (4), p. 4 — |μ₃³(p)| ≤ 2√((k+2)/k)·(k−1)/(k+3)·μ₂³(p) for 1/(k−1)-concave p
-- statement:
--   Let $k\ge1$ be an integer and let $p$ be a $\tfrac1{k-1}$-concave probability density on $\mathbb R$ (for $k=1$: $\infty$-concave). Then
--   $$\bigl|\mu_3^3(p)\bigr|\ \le\ 2\sqrt{\frac{k+2}{k}}\;\frac{k-1}{k+3}\;\mu_2^3(p),$$
--   where $\mu_3^3(p)$ is the third central moment and $\mu_2^3(p)=(\mu_2^2(p))^{3/2}$ the cube of the standard deviation.
--
--   This is the first half of Proposition 1. With $k=n$, applied to the marginal of $K^\circ(x)$, it yields the self-concordance inequality (1) in Theorem 2. It is sharp (equality for $k\,t^{k-1}\mathbb 1_{[0,1]}$), and as $k\to\infty$ it recovers the bound $|\mu_3^3|\le2\mu_2^3$ for log-concave densities.
--
--   **Formalization Note.** $s$-concavity is quantified over support points (the literal Definition 5 admits no density), with index $m=k-1$ and $m=0$ the $\max$ clause. For $k=1$ the right-hand side is $0$.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 4, Proposition 1, inequality (4)

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

open MeasureTheory

namespace UniversalBarrier.NSC

theorem proposition_1_ineq4 (k : ℕ) (hk : 1 ≤ k) (p : ℝ → ℝ) (hp0 : ∀ t, 0 ≤ p t)
    (hp1 : ∫ t, p t = 1) (hpc : IsOneOverMConcave (k - 1) p) :
    |mu3cube p| ≤ 2 * Real.sqrt (((k : ℝ) + 2) / k) * (((k : ℝ) - 1) / ((k : ℝ) + 3))
      * Real.sqrt (mu2sq p) ^ 3 := by sorry

end UniversalBarrier.NSC
